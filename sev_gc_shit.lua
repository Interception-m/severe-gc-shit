local SevereGC = {}
SevereGC.Version = "1.3.3"

local TWO32 = 4294967296
local TWO47 = 140737488355328

local b_u8 = buffer.readu8
local b_i32 = buffer.readi32
local b_u32 = buffer.readu32
local b_f32 = buffer.readf32
local b_f64 = buffer.readf64
local b_str = buffer.readstring
local b_len = buffer.len
local b_create = buffer.create
local b_copy = buffer.copy
local b_wu32 = buffer.writeu32
local b_wi32 = buffer.writei32
local b_wf32 = buffer.writef32
local b_wf64 = buffer.writef64
local band = bit32.band
local bxor = bit32.bxor
local clock = os.clock

local memLib = memory
local memRead = memLib and (memLib.readbuffer or memLib.read_buffer)
local memWrite = memLib and (memLib.writebuffer or memLib.write_buffer)
local memRtti = memLib and memLib.rtti
local toUserdata = pointer_to_userdata
local waitFn = (task and task.wait) or wait


local Layout = nil
local VMs = {}
local Current = nil
local Notes = {}
local Status = "not attached"

local function note(s)
	Notes[#Notes + 1] = s
	if #Notes > 200 then table.remove(Notes, 1) end
	local cb = SevereGC.OnNote
	if cb then pcall(cb, s) end
end

local function wipe(t)
	for k in next, t do t[k] = nil end
end

local function rd(addr, size)
	if type(addr) ~= "number" or addr < 0x10000 or addr + size > TWO47 or size <= 0 or size > 0x800000 then return nil end
	local ok, b = pcall(memRead, addr, size)
	if ok and type(b) == "buffer" and b_len(b) >= size then return b end
	return nil
end

local function rdInst(inst, off, size)
	local ok, b = pcall(memRead, inst, off, size)
	if ok and type(b) == "buffer" and b_len(b) >= size then return b end
	return nil
end

local function q(b, o)
	local hi = b_u32(b, o + 4)
	if hi >= 0x8000 then return -1 end
	return hi * TWO32 + b_u32(b, o)
end

local function isptr(v)
	return v > 0x10000 and v < TWO47 and v % 8 == 0
end

local function decodePtr(F, b, o, enc)
	local lo, hi = b_u32(b, o), b_u32(b, o + 4)
	if enc == 0 then
		if hi >= 0x8000 then return 0 end
		return hi * TWO32 + lo
	end
	local flo = F % TWO32
	local fhi = (F - flo) / TWO32
	local rlo, rhi
	if enc == 1 then
		rlo = flo + lo
		local c = 0
		if rlo >= TWO32 then rlo -= TWO32 c = 1 end
		rhi = (fhi + hi + c) % TWO32
	elseif enc == 2 then
		rlo = flo - lo
		local bo = 0
		if rlo < 0 then rlo += TWO32 bo = 1 end
		rhi = (fhi - hi - bo) % TWO32
	elseif enc == 3 then
		rlo = lo - flo
		local bo = 0
		if rlo < 0 then rlo += TWO32 bo = 1 end
		rhi = (hi - fhi - bo) % TWO32
	else
		rlo = bxor(lo, flo)
		rhi = bxor(hi, fhi)
	end
	if rhi >= 0x8000 then return 0 end
	return rhi * TWO32 + rlo
end

local function readPtrAt(addr, enc)
	local b = rd(addr, 8)
	if not b then return 0 end
	return decodePtr(addr, b, 0, enc or 0)
end

local function newCtx(opts)
	opts = opts or {}
	local now = clock()
	local ctx = {
		yield = opts.Yield ~= false,
		slice = (opts.SliceMs or SevereGC.SliceMs or 40) / 1000,
		grace = (opts.GraceMs or SevereGC.GraceMs or 150) / 1000,
		start = now,
		t0 = now,
		deadline = opts.BudgetMs and (now + opts.BudgetMs / 1000) or nil,
		truncated = false,
		maxPages = opts.MaxPages,
	}
	return ctx
end

local function step(ctx)
	local now = clock()
	if ctx.deadline and now > ctx.deadline then
		ctx.truncated = true
		return false
	end
	if ctx.yield and now - ctx.start >= ctx.grace and now - ctx.t0 >= ctx.slice then
		if coroutine.isyieldable() and waitFn then
			waitFn()
			ctx.yields = (ctx.yields or 0) + 1
			ctx.yieldTime = (ctx.yieldTime or 0) + (clock() - now)
		end
		ctx.t0 = clock()
	end
	return true
end

local function moduleRange(v)
	local base = memLib and memLib.base
	if type(base) ~= "number" then return false end
	return v >= base and v < base + 0x10000000
end

local function instAddr(inst)
	local b = rdInst(inst, 8, 8)
	if not b then return nil end
	local a = q(b, 0)
	if not isptr(a) then return nil end
	local s = rd(a + 8, 8)
	if s and q(s, 0) == a then return a end
	return nil
end

local function looksInstance(a)
	if not isptr(a) then return false end
	local b = rd(a + 8, 8)
	return b ~= nil and q(b, 0) == a
end

local function isInstanceValue(v)
	return type(v) == "userdata" and typeof and typeof(v) == "Instance"
end

local ClassCache = {}
local function instanceClass(a)
	if not isptr(a) then return nil end
	local c = ClassCache[a]
	if c then return c end
	if memRtti then
		local ok, r = pcall(memRtti, a)
		if ok and type(r) == "string" then
			local name = string.match(r, "%.%?AV([%w_]+)@RBX@@") or string.match(r, "RBX::([%w_]+)") or string.match(r, "([%w_]+)@RBX")
			if name then ClassCache[a] = name return name end
		end
	end
	if toUserdata and looksInstance(a) then
		local ok, inst = pcall(toUserdata, a)
		if ok and inst then
			local ok2, cn = pcall(function() return inst.ClassName end)
			if ok2 and type(cn) == "string" then ClassCache[a] = cn return cn end
		end
	end
	return nil
end

local resolveVM, pickVM
local ensureLazy
local VMsPartial = false

local function scriptContext()
	local ok, sc = pcall(function() return game:GetService("ScriptContext") end)
	if ok and sc then return sc end
	ok, sc = pcall(function() return game:FindFirstChildOfClass("ScriptContext") end)
	if ok and sc then return sc end
	local ok2, kids = pcall(function() return game:GetChildren() end)
	if ok2 then
		for _, c in kids do
			local ok3, cn = pcall(function() return c.ClassName end)
			if ok3 and cn == "ScriptContext" then return c end
		end
	end
	return nil
end

local function strtIn(b, span)
	local hits = {}
	for so = 0, span - 16, 8 do
		local h = q(b, so)
		if isptr(h) then
			local nuse = b_u32(b, so + 8)
			local size = b_u32(b, so + 12)
			if size >= 1024 and size <= 16777216 and band(size, size - 1) == 0 and nuse > 64 and nuse <= size * 4 then
				local hb = rd(h, 512)
				if hb then
					local good = 0
					for i = 0, 63 do
						local t = q(hb, i * 8)
						if t ~= 0 then
							if not isptr(t) then good = -1000 break end
							good += 1
						end
					end
					if good >= 4 then hits[#hits + 1] = so end
				end
			end
		end
	end
	return hits
end

local function pageVotes(G)
	local gb = rd(G, 0x800)
	if not gb then return 0 end
	local hits = 0
	for o = 0, 0x800 - 8, 8 do
		local v = q(gb, o)
		if isptr(v) then
			local hb = rd(v, 0x48)
			if hb then
				for k = 4, 17 do
					local x = b_i32(hb, k * 4)
					if x == 16360 or x == 32744 then hits += 1 break end
				end
			end
		end
	end
	return hits
end

local function probeVM(A)
	local hb0 = rd(A, 16)
	if not hb0 then return nil end
	local h = q(hb0, 0)
	local size = b_u32(hb0, 12)
	local buckets = rd(h, 8 * 256)
	if not buckets then return nil end
	local tag, n = nil, 0
	for i = 0, 255 do
		local t = q(buckets, i * 8)
		if isptr(t) then
			local th = rd(t, 0x20)
			if th then
				local tt = b_u8(th, 1)
				if tag == nil then tag = tt elseif tag ~= tt then return nil end
				if b_u32(th, 0x14) > 0x4000000 then return nil end
				n += 1
				if n >= 12 then break end
			end
		end
	end
	if not tag or n < 4 then return nil end
	local winBase = A - 0x300
	local w = rd(winBase, 0xC00)
	if not w then
		winBase = A - 0x10
		w = rd(winBase, 0x910)
	end
	if not w then return nil end
	for wo = 0, b_len(w) - 8, 8 do
		local M = q(w, wo)
		if isptr(M) and M < A and A - M <= 0x400 then
			local mb = rd(M, 0x100)
			if mb then
				for lo = 0, 0xF8, 8 do
					local B = q(mb, lo)
					if B <= A and A - B <= 0x100 and B > M and winBase + wo >= B and b_u8(mb, 1) ~= tag then
						if pageVotes(B) >= 8 then
							return {
								G = B,
								main = M,
								strt = A - B,
								lGlobal = lo,
								mainOff = winBase + wo - B,
								strTag = tag,
								thrTag = b_u8(mb, 1),
								strSize = size,
							}
						end
					end
				end
			end
		end
	end
	return nil
end


local function readSC(sc)
	return rdInst(sc, 0, 0x1000) or rdInst(sc, 0, 0x800) or rdInst(sc, 0, 0x400)
end

local function followPath(sc, path)
	local node = nil
	local b = readSC(sc)
	if not b then return nil end
	for i, off in path.offs do
		if off + 8 > b_len(b) then return nil end
		node = q(b, off)
		if not isptr(node) then return nil end
		if i < #path.offs then
			b = rd(node, 0x200)
			if not b then return nil end
		end
	end
	if not node then return nil end
	return probeVM(node + path.so)
end

local function discoverVMs(sc, opts)
	opts = opts or {}
	local found, byG = {}, {}
	local function add(vm)
		if vm and not byG[vm.G] then
			byG[vm.G] = vm
			found[#found + 1] = vm
			return true
		end
		return false
	end
	local first = readSC(sc)
	if not first then
		note("ScriptContext unreadable")
		return found
	end
	local maxNodes = opts.MaxNodes or 80000
	local maxDepth = opts.MaxDepth or 4
	local qa, qd, qparent, qoff = {}, {}, {}, {}
	local seen = {}
	for o = 0, b_len(first) - 8, 8 do
		local v = q(first, o)
		if isptr(v) and not seen[v] and not moduleRange(v) then
			seen[v] = true
			qa[#qa + 1] = v
			qd[#qd + 1] = 1
			qparent[#qparent + 1] = 0
			qoff[#qoff + 1] = o
		end
	end
	local ctx = newCtx({ BudgetMs = opts.BudgetMs or 25000 })
	local head = 1
	local lastFound = 0
	local thrTag, lGlobal, strtOff
	local tried = {}
	local accepted = nil
	local function consider(vm)
		if opts.Accept and not accepted then
			local okA, res = pcall(opts.Accept, vm)
			if okA and res then accepted = vm end
		end
	end
	local function pathTo(k, extra)
		local offs = {}
		while k > 0 do
			table.insert(offs, 1, qoff[k])
			k = qparent[k]
		end
		if extra then offs[#offs + 1] = extra end
		return offs
	end
	while head <= #qa and head <= maxNodes do
		local node, dep = qa[head], qd[head]
		local b = rd(node, 0x200)
		if b then
			for _, so in strtIn(b, 0x100) do
				local vm = probeVM(node + so)
				if vm and not byG[vm.G] then
					vm.path = { offs = pathTo(head), so = so }
					add(vm)
					lastFound = head
					thrTag, lGlobal, strtOff = vm.thrTag, vm.lGlobal, vm.strt
					consider(vm)
					break
				end
			end
			if thrTag and b_u8(b, 1) == thrTag and lGlobal + 8 <= 0x200 then
				local g = q(b, lGlobal)
				if isptr(g) and not byG[g] and not tried[g] then
					tried[g] = true
					local vm = probeVM(g + strtOff)
					if vm and vm.G == g and not byG[g] then
						vm.path = { offs = pathTo(head, lGlobal), so = strtOff }
						add(vm)
						lastFound = head
						consider(vm)
					end
				end
			end
			if dep < maxDepth and #qa < maxNodes then
				for o = 0, 0x200 - 8, 8 do
					local v = q(b, o)
					if isptr(v) and not seen[v] and not moduleRange(v) then
						seen[v] = true
						qa[#qa + 1] = v
						qd[#qd + 1] = dep + 1
						qparent[#qparent + 1] = head
						qoff[#qoff + 1] = o
						if #qa >= maxNodes then break end
					end
				end
			end
		end
		head += 1
		if accepted then break end
		if #found > 0 and qd[head] and qd[head] > 3 and head - lastFound > (opts.Patience or 30000) then break end
		if head % 64 == 0 and not step(ctx) then break end
	end
	note(string.format("vm search: %d nodes, %d vms%s", head - 1, #found, accepted and " (stopped at the first game VM)" or ""))
	return found, accepted
end

local function derivePages(G)
	local gb = rd(G, 0x800)
	if not gb then return nil, "global_State unreadable" end
	local votes = {}
	local hdrAt = {}
	local function hdrOf(v)
		local b = hdrAt[v]
		if b == nil then
			b = rd(v, 0x50) or false
			hdrAt[v] = b
		end
		return b or nil
	end
	for o = 0, 0x800 - 8, 8 do
		local v = q(gb, o)
		if isptr(v) then
			local hb = hdrOf(v)
			if hb then
				for k = 4, 17 do
					local x = b_i32(hb, k * 4)
					if x == 16360 or x == 32744 then votes[k * 4] = (votes[k * 4] or 0) + 1 end
				end
			end
		end
	end
	local ps, best = nil, 0
	for off, c in votes do
		if c > best then best, ps = c, off end
	end
	if not ps or best < 8 then return nil, "no lua_Page pageSize field" end
	local bs = ps + 4
	local heads = {}
	for o = 0, 0x800 - 8, 8 do
		local v = q(gb, o)
		if isptr(v) then
			local hb = hdrOf(v)
			if hb then
				local x, y = b_i32(hb, ps), b_i32(hb, bs)
				if x >= 1024 and x <= 0x100000 and y >= 8 and y <= 0x10000 and y % 8 == 0 then
					heads[#heads + 1] = { off = o, page = v }
				end
			end
		end
	end
	if #heads < 8 then return nil, "too few page lists in global_State" end
	local sizes = { [16360] = true, [32744] = true }
	local sizeVotes = {}
	for _, h in heads do
		local hb = hdrOf(h.page)
		if hb then
			local x = b_i32(hb, ps)
			sizeVotes[x] = (sizeVotes[x] or 0) + 1
		end
	end
	for x, c in sizeVotes do
		if c >= 3 then sizes[x] = true end
	end
	local links = {}
	for o = 0, ps - 8, 8 do links[#links + 1] = o end
	local dataCands = {}
	for d = bs + 12, bs + 0x2C, 4 do
		if d % 8 == 0 then dataCands[#dataCands + 1] = d end
	end
	local scores = {}
	local nzFn = {}
	local tested = 0
	for i = 1, #heads, math.max(1, #heads // 16) do
		local pg = heads[i].page
		local hb = hdrOf(pg)
		if hb then
			local pgs, bsz = b_i32(hb, ps), b_i32(hb, bs)
			if pgs >= 1024 and pgs <= 0x10000 and bsz >= 8 and bsz % 8 == 0 then
				local buf = rd(pg, pgs)
				if buf then
					tested += 1
					for _, data in dataCands do
						local cap = (pgs - data) // bsz
						for fo = bs + 4, data - 4, 4 do
							local fn = b_i32(buf, fo)
							if fn >= -bsz and fn <= (cap - 1) * bsz and (fn < 0 or fn % bsz == 0) then
								local live, metas = 0, 0
								local at = data + fn + bsz
								local stop = data + cap * bsz
								while at + 8 <= stop do
									if b_u8(buf, at + 1) ~= 0 then live += 1 end
									if q(buf, at) == pg then metas += 1 end
									at += bsz
								end
								for bo = bs + 4, data - 4, 4 do
									if bo ~= fo then
										local bb = b_i32(buf, bo)
										if bb > 0 and (bb == live or bb == metas) then
											local key = data * 1000000 + fo * 1000 + bo
											scores[key] = (scores[key] or 0) + 1
											if fn ~= 0 then nzFn[key] = true end
										end
									end
								end
							end
						end
					end
				end
			end
		end
	end
	local bestKey, bestScore = nil, 0
	for key, c in scores do
		local better = c > bestScore
		if not better and c == bestScore and bestKey then
			local a, b = nzFn[key] == true, nzFn[bestKey] == true
			better = (a and not b) or (a == b and key < bestKey)
		end
		if better then bestKey, bestScore = key, c end
	end
	if not bestKey or bestScore * 2 < tested then return nil, "page freeNext/busyBlocks not found" end
	local data = bestKey // 1000000
	local fo = (bestKey // 1000) % 1000
	local bo = bestKey % 1000
	return {
		ps = ps,
		bs = bs,
		data = data,
		fn = fo,
		bb = bo,
		links = links,
		heads = heads,
		sizes = sizes,
	}
end

local function pageRange(buf, P, pgs, bsz)
	local blen = b_len(buf)
	if blen < P.data + 8 or bsz < 8 then return nil end
	if b_i32(buf, P.ps) ~= pgs or b_i32(buf, P.bs) ~= bsz then return nil end
	local single = pgs == P.data + bsz
	if bsz % 8 ~= 0 and not single then return nil end
	if not (P.sizes[pgs] or single) then return nil end
	local cap = (pgs - P.data) // bsz
	if cap < 1 then return nil end
	local fn = b_i32(buf, P.fn)
	if fn < -bsz or fn > (cap - 1) * bsz then return nil end
	if fn >= 0 and fn % bsz ~= 0 then return nil end
	local bb = b_i32(buf, P.bb)
	if bb < 0 or bb > cap then return nil end
	local at = P.data + fn + bsz
	local stop = math.min(P.data + cap * bsz, blen)
	if at < P.data then return nil end
	return at, stop
end

local function pageIsMeta(buf, pg, P, pgs, bsz)
	local at, stop = pageRange(buf, P, pgs, bsz)
	if not at then return false end
	while at + 8 <= stop do
		if q(buf, at) == pg then return true end
		at += bsz
	end
	return false
end

local function vmHeads(vm, P)
	if vm.gcHeads then return vm.gcHeads, vm.ngHeads end
	local gb = rd(vm.G, 0x800)
	local gcH, ngH = {}, {}
	if gb then
		for o = 0, 0x800 - 8, 8 do
			local v = q(gb, o)
			if isptr(v) then
				local hb = rd(v, P.ps + 8)
				if hb then
					local pgs, bsz = b_i32(hb, P.ps), b_i32(hb, P.bs)
					if pgs >= 1024 and pgs <= 0x10000 and bsz >= 8 and bsz <= 0x10000 and bsz % 8 == 0 then
						local buf = rd(v, pgs)
						if buf and pageRange(buf, P, pgs, bsz) then
							if pageIsMeta(buf, v, P, pgs, bsz) then ngH[#ngH + 1] = o else gcH[#gcH + 1] = o end
						end
					end
				end
			end
		end
	end
	vm.gcHeads, vm.ngHeads = gcH, ngH
	return gcH, ngH
end

local function forEachPage(vm, kind, visit, ctx)
	local P = Layout.pages
	local gcH, ngH = vmHeads(vm, P)
	local headOffs = kind == "gc" and gcH or ngH
	local stack = {}
	for _, o in headOffs do
		local v = readPtrAt(vm.G + o, 0)
		if isptr(v) then stack[#stack + 1] = v end
	end
	local seen = {}
	local count = 0
	local readSize = 16360
	while #stack > 0 do
		local pg = table.remove(stack)
		if not seen[pg] then
			seen[pg] = true
			local buf = rd(pg, readSize)
			local pgs, bsz
			if buf then
				pgs, bsz = b_i32(buf, P.ps), b_i32(buf, P.bs)
				if pgs > readSize and pgs <= 0x10000 then
					buf = rd(pg, pgs)
				elseif pgs > 0x10000 then
					buf = rd(pg, P.data + math.min(bsz, 0x1000))
				end
			else
				local hb = rd(pg, P.data + 0x40)
				if hb then
					pgs, bsz = b_i32(hb, P.ps), b_i32(hb, P.bs)
					if pgs <= 0x10000 then buf = rd(pg, pgs) else buf = rd(pg, P.data + math.min(bsz, 0x1000)) end
				end
			end
			if buf and pgs and pageRange(buf, P, pgs, bsz) then
				for _, lo in P.links do
					local nx = q(buf, lo)
					if isptr(nx) and not seen[nx] then stack[#stack + 1] = nx end
				end
				local meta = pgs <= 0x10000 and pageIsMeta(buf, pg, P, pgs, bsz)
				local want = (kind == "gc" and not meta) or (kind == "ng" and meta)
				if want then
					count += 1
					if visit(pg, buf, pgs, bsz) == true then return true end
					if ctx then
						if ctx.maxPages and count >= ctx.maxPages then ctx.truncated = true return false end
						if not step(ctx) then return false end
					end
				end
			end
		end
	end
	return false
end

local function forEachObject(vm, tagFilter, visit, ctx)
	local P = Layout.pages
	local data = P.data
	return forEachPage(vm, "gc", function(pg, buf, pgs, bsz)
		local at, stop = pageRange(buf, P, pgs, bsz)
		if not at then return false end
		while at + 2 <= stop do
			local tt = b_u8(buf, at + 1)
			if tt ~= 0 and (tagFilter == nil or tagFilter[tt]) then
				if visit(pg + at, tt, buf, at, bsz) == true then return true end
			end
			at += bsz
		end
		return false
	end, ctx)
end

local function listPages(vm, kind, ctx)
	local P = Layout.pages
	local gcH, ngH = vmHeads(vm, P)
	local heads = kind == "gc" and gcH or ngH
	local stack, seen, out = {}, {}, {}
	for _, o in heads do
		local v = readPtrAt(vm.G + o, 0)
		if isptr(v) then stack[#stack + 1] = v end
	end
	local hdr = P.data + 8
	while #stack > 0 do
		local pg = table.remove(stack)
		if not seen[pg] then
			seen[pg] = true
			local hb = rd(pg, hdr)
			if hb then
				local pgs, bsz = b_i32(hb, P.ps), b_i32(hb, P.bs)
				if pageRange(hb, P, pgs, bsz) then
					for _, lo in P.links do
						local nx = q(hb, lo)
						if isptr(nx) and not seen[nx] then stack[#stack + 1] = nx end
					end
					out[#out + 1] = { pg, pgs, bsz }
				end
			end
			if ctx and #out % 512 == 0 and not step(ctx) then break end
		end
	end
	return out
end

local function sampleCensus(vm, perTag, maxPages)
	local samples, counts, sizes = {}, {}, {}
	local tagOf = {}
	local nKnown = 0
	local P = Layout.pages
	local ctx = newCtx({ Yield = true })
	local pages = listPages(vm, "gc", ctx)
	maxPages = maxPages or 600
	local stride = math.max(1, #pages / maxPages)
	local perPage = {}
	local idx = 1
	local visited = 0
	while idx <= #pages do
		local e = pages[math.floor(idx)]
		idx += stride
		local pg, pgs, bsz = e[1], e[2], e[3]
		local buf = pgs <= 0x10000 and rd(pg, pgs) or rd(pg, P.data + math.min(bsz, 0x1000))
		local at, stop
		if buf then at, stop = pageRange(buf, P, pgs, bsz) end
		if at and not (pgs <= 0x10000 and pageIsMeta(buf, pg, P, pgs, bsz)) then
			visited += 1
			local blen = b_len(buf)
			wipe(perPage)
			while at + 2 <= stop do
				local tt = b_u8(buf, at + 1)
				if tt ~= 0 then
					local addr = pg + at
					counts[tt] = (counts[tt] or 0) + 1
					local sz = sizes[tt]
					if not sz then sz = {} sizes[tt] = sz end
					sz[bsz] = (sz[bsz] or 0) + 1
					if nKnown < 200000 then
						tagOf[addr] = tt
						nKnown += 1
					end
					local list = samples[tt]
					if not list then list = {} samples[tt] = list end
					local pp = perPage[tt] or 0
					if #list < perTag and pp < 4 then
						perPage[tt] = pp + 1
						local span = math.min(bsz, 0x100, blen - at)
						local sb = b_create(span)
						b_copy(sb, 0, buf, at, span)
						list[#list + 1] = { a = addr, b = sb, bs = bsz }
					end
				end
				at += bsz
			end
		end
		if not step(ctx) then break end
	end
	note(string.format("census: %d of %d gc pages", visited, #pages))
	return samples, counts, sizes, tagOf, pages
end

local TagCache = {}
local TagCacheN = 0
local function tagAt(a, known)
	if not isptr(a) then return nil end
	if known then
		local t = known[a]
		if t then return t end
	end
	if not known then
		local b = rd(a, 8)
		return b and b_u8(b, 1) or nil
	end
	local t = TagCache[a]
	if t ~= nil then return t or nil end
	local b = rd(a, 8)
	t = b and b_u8(b, 1) or false
	if TagCacheN < 100000 then
		TagCache[a] = t
		TagCacheN += 1
	end
	return t or nil
end

local function tvalueOk(b, o, n, tags)
	for i = 0, n - 1 do
		local tt = b_i32(b, o + i * 16 + 12)
		if tt < 0 or tt > 31 then return false end
		if tt == tags.string then
			if not isptr(q(b, o + i * 16)) then return false end
		end
	end
	return true
end

local function deriveTable(sm, tags, known)
	local S = tags.string
	local best
	for a = 2, 7 do
		for m = 2, 7 do
			if a ~= m then
				local nt, ok = 0, 0
				for _, s in sm do
					local lsz = b_u8(s.b, a)
					if lsz >= 1 and lsz <= 24 then
						nt += 1
						if b_u8(s.b, m) == band(2 ^ lsz - 1, 255) then ok += 1 end
					end
				end
				if nt >= 8 and ok >= nt * 0.98 and (not best or nt > best.nt) then best = { a = a, m = m, nt = nt } end
			end
		end
	end
	if not best then return nil, "table lsizenode not found" end
	local lszOff = best.a
	local span = sm[1].bs
	local need = math.min(span, 0x40)
	local full = {}
	for _, s in sm do
		if b_len(s.b) >= need and s.bs == span then full[#full + 1] = s end
	end
	sm = full
	if #sm < 8 then return nil, "table samples too short" end
	local nodeOff, nodeScore = nil, 0
	for o = 8, math.min(span, 0x40) - 8, 8 do
		local score, used = 0, 0
		for _, s in sm do
			if used >= 40 then break end
			local lsz = b_u8(s.b, lszOff)
			if lsz >= 1 and lsz <= 16 then
				local np = q(s.b, o)
				if isptr(np) then
					used += 1
					local cnt = math.min(2 ^ lsz, 8)
					local nb = rd(np, cnt * 32)
					if nb then
						for i = 0, cnt - 1 do
							local ktt = band(b_u32(nb, i * 32 + 28), 15)
							if ktt == S and isptr(q(nb, i * 32 + 16)) then score += 1 end
						end
					end
				end
			end
		end
		if score > nodeScore then nodeOff, nodeScore = o, score end
	end
	if not nodeOff or nodeScore < 10 then return nil, "table node field not found" end
	local dummyCount = {}
	for _, s in sm do
		if b_u8(s.b, lszOff) == 0 then
			local v = q(s.b, nodeOff)
			dummyCount[v] = (dummyCount[v] or 0) + 1
		end
	end
	local dummy, dc = 0, 0
	for v, c in dummyCount do
		if c > dc then dummy, dc = v, c end
	end
	local metaOff, metaScore = nil, 0
	for o = 8, math.min(span, 0x40) - 8, 8 do
		if o ~= nodeOff then
			local nz, bad = 0, 0
			for i, s in sm do
				if i > 300 then break end
				local v = q(s.b, o)
				if v ~= 0 then
					if not isptr(v) then bad += 1 break end
					if tagAt(v, known) == tags.table then nz += 1 else bad += 1 break end
				end
			end
			if bad == 0 and nz > metaScore then metaOff, metaScore = o, nz end
		end
	end
	local live = {}
	for i, s in sm do
		if i > 400 then break end
		local lb = rd(s.a, span)
		if lb and b_u8(lb, 1) == tags.table then live[#live + 1] = { a = s.a, b = lb } end
	end
	local arrOff, arrEnc, sizeOff, arrScore = nil, 0, nil, 0
	for o = 8, math.min(span, 0x40) - 8, 8 do
		if o ~= nodeOff and o ~= metaOff then
			for enc = 0, 4 do
				for c = 8, math.min(span, 0x40) - 4, 4 do
					if c < o or c >= o + 8 then
						if not (c >= nodeOff and c < nodeOff + 8) and not (metaOff and c >= metaOff and c < metaOff + 8) then
							local good, bad, used = 0, 0, 0
							for _, s in live do
								if used >= 120 then break end
								local n = b_i32(s.b, c)
								local raw = q(s.b, o)
								local ap = decodePtr(s.a + o, s.b, o, enc)
								if n > 0 and n <= 100000 then
									used += 1
									if isptr(ap) then
										local k = math.min(n, 16)
										local ab = rd(ap - 8, k * 16 + 8)
										local okA = false
										if ab and tvalueOk(ab, 8, k, tags) then
											local nonNil = false
											for i = 0, k - 1 do
												if b_i32(ab, 8 + i * 16 + 12) ~= 0 then nonNil = true break end
											end
											local hdr = q(ab, 0)
											local small = n * 16 + 8 <= 1024
											local okHdr = not small or (isptr(hdr) and hdr < ap and ap - hdr <= 0x10000)
											okA = nonNil and okHdr
										end
										if okA then good += 1 else bad += 1 end
									else
										bad += 1
									end
								elseif n == 0 then
									if ap ~= 0 and raw ~= 0 and enc == 0 then bad += 1 end
								else
									bad += 1
								end
								if bad > 8 and bad > good then break end
							end
							if good >= 3 and bad <= (good + bad) * 0.15 then
								local better = good > arrScore
								if not better and good == arrScore and arrOff then
									better = enc < arrEnc or (enc == arrEnc and c < sizeOff)
								end
								if better then arrOff, arrEnc, sizeOff, arrScore = o, enc, c, good end
							end
						end
					end
				end
			end
		end
	end
	if not arrOff then note("table array part not derived (" .. #live .. " live samples)") end
	return {
		lsz = lszOff,
		mask = best.m,
		node = nodeOff,
		dummy = dummy,
		meta = metaOff,
		array = arrOff,
		arrayEnc = arrEnc,
		sizearray = sizeOff,
		span = span,
	}
end

local function deriveClosure(sm, tags, known)
	local n = #sm
	local envOff
	for o = 8, 0x30, 8 do
		local ok, used = 0, 0
		for i, s in sm do
			if i > 150 then break end
			if o + 8 <= b_len(s.b) then
				used += 1
				if tagAt(q(s.b, o), known) == tags.table then ok += 1 end
			end
		end
		if used > 20 and ok >= used * 0.9 then envOff = o break end
	end
	if not envOff then return nil, "closure env field not found" end
	local isCOff
	local cLike, luaLike = {}, {}
	for _, s in sm do
		local hasMod = false
		for o = 8, math.min(b_len(s.b), 0x40) - 8, 8 do
			if o ~= envOff and moduleRange(q(s.b, o)) then hasMod = true break end
		end
		if hasMod then cLike[#cLike + 1] = s else luaLike[#luaLike + 1] = s end
	end
	if #cLike >= 1 and #luaLike >= 10 then
		for b = 2, 7 do
			local cOne, luaZero = 0, 0
			for _, s in cLike do if b_u8(s.b, b) == 1 then cOne += 1 end end
			for _, s in luaLike do if b_u8(s.b, b) == 0 then luaZero += 1 end end
			if cOne >= #cLike * 0.9 and luaZero >= #luaLike * 0.97 then isCOff = b break end
		end
	end
	if not isCOff then return nil, string.format("closure isC byte not found (%d C-like, %d Lua-like samples)", #cLike, #luaLike) end
	local protoOff, protoTag, protoEnc
	for o = 8, 0x30, 8 do
		if o ~= envOff then
			for enc = 0, 4 do
				local tc, used = {}, 0
				for i, s in sm do
					if used >= 150 then break end
					if b_u8(s.b, isCOff) == 0 and o + 8 <= b_len(s.b) then
						used += 1
						local t = tagAt(decodePtr(s.a + o, s.b, o, enc), known)
						if t then tc[t] = (tc[t] or 0) + 1 end
					end
				end
				for t, c in tc do
					if used > 20 and c >= used * 0.9 and t ~= tags.string and t ~= tags.table and t ~= tags.func and t ~= tags.thread and t ~= 0 then
						protoOff, protoTag, protoEnc = o, t, enc
					end
				end
				if protoOff then break end
			end
			if protoOff then break end
		end
	end
	if not protoOff then return nil, "closure proto field not found" end
	local protoHdr = {}
	local used = 0
	for i, s in sm do
		if used >= 200 then break end
		if b_u8(s.b, isCOff) == 0 then
			local pb = rd(decodePtr(s.a + protoOff, s.b, protoOff, protoEnc), 8)
			if pb then
				used += 1
				protoHdr[#protoHdr + 1] = { s = s, pb = pb }
			end
		end
	end
	local eqPairs = {}
	for cb = 2, 7 do
		if cb ~= isCOff then
			for pb = 2, 7 do
				local eq, nz = 0, 0
				for _, e in protoHdr do
					local cv, pv = b_u8(e.s.b, cb), b_u8(e.pb, pb)
					if cv == pv then
						eq += 1
						if cv ~= 0 then nz += 1 end
					end
				end
				if #protoHdr >= 20 and eq >= #protoHdr * 0.97 and nz >= 5 then
					eqPairs[#eqPairs + 1] = { cb = cb, pb = pb, nz = nz }
				end
			end
		end
	end
	local nupC, nupP, bestFit = nil, nil, -1
	for _, pr in eqPairs do
		for base = 0x18, 0x30, 8 do
			local fit = 0
			for _, e in protoHdr do
				local slack = e.s.bs - (base + 16 * b_u8(e.s.b, pr.cb))
				if slack >= 0 and slack < 32 then fit += 1 end
			end
			if fit > bestFit then nupC, nupP, bestFit = pr.cb, pr.pb, fit end
		end
	end
	if not nupC or bestFit < #protoHdr * 0.9 then
		return nil, string.format("closure nupvalues byte not found (%d equal byte pairs, best size fit %d/%d)", #eqPairs, bestFit, #protoHdr)
	end
	local stackC, stackP, stackNz = nil, nil, 0
	for _, pr in eqPairs do
		if pr.cb ~= 2 and pr.pb ~= 2 and pr.cb ~= nupC and pr.pb ~= nupP and pr.nz > stackNz then
			local big = 0
			for _, e in protoHdr do if b_u8(e.s.b, pr.cb) < 128 then big += 1 end end
			if big >= #protoHdr * 0.99 then stackC, stackP, stackNz = pr.cb, pr.pb, pr.nz end
		end
	end
	local upOff
	local tried = {}
	for o = protoOff + 8, 0x48, 8 do
		local ok, tot, over = 0, 0, 0
		for _, s in sm do
			if b_u8(s.b, isCOff) == 0 then
				local nup = b_u8(s.b, nupC)
				if nup >= 1 and o + nup * 16 <= b_len(s.b) then
					tot += 1
					if o + nup * 16 > s.bs then
						over += 1
					elseif tvalueOk(s.b, o, nup, tags) then
						ok += 1
					end
				end
			end
		end
		tried[#tried + 1] = string.format("0x%x:%d/%d", o, ok, tot)
		if tot >= 10 and ok >= tot * 0.95 then upOff = o break end
	end
	if not upOff then
		return nil, string.format("closure upvalue array not found (env 0x%x isC %d proto 0x%x enc %d nup %d; %s)", envOff, isCOff, protoOff, protoEnc, nupC, table.concat(tried, " "))
	end
	local uvTagCount = {}
	for i, s in sm do
		if i > 400 then break end
		if b_u8(s.b, isCOff) == 0 then
			local nup = b_u8(s.b, nupC)
			for k = 0, nup - 1 do
				local at = upOff + k * 16
				if at + 16 <= b_len(s.b) then
					local tt = b_i32(s.b, at + 12)
					if tt > tags.thread and tt ~= protoTag then
						local v = q(s.b, at)
						if tagAt(v, known) == tt then uvTagCount[tt] = (uvTagCount[tt] or 0) + 1 end
					end
				end
			end
		end
	end
	local uvTag, uvc = nil, 0
	for t, c in uvTagCount do
		if c > uvc then uvTag, uvc = t, c end
	end
	local cF, cName, cUp
	local cs = {}
	for _, s in sm do
		if b_u8(s.b, isCOff) == 1 then cs[#cs + 1] = s end
	end
	if #cs > 0 then
		for o = 8, 0x40, 8 do
			local hits, tot = 0, 0
			for _, s in cs do
				if o + 8 <= b_len(s.b) then
					tot += 1
					if moduleRange(q(s.b, o)) then hits += 1 end
				end
			end
			if tot > 0 and hits >= tot * 0.9 then cF = o break end
		end
		for o = 8, 0x40, 8 do
			if o ~= envOff and o ~= cF then
				local hits, tot = 0, 0
				for _, s in cs do
					if o + 8 <= b_len(s.b) then
						tot += 1
						if tagAt(q(s.b, o), known) == tags.string then hits += 1 end
					end
				end
				if tot > 0 and hits >= tot * 0.5 then cName = o break end
			end
		end
		local after = math.max(envOff, cF or 0, cName or 0) + 8
		for o = after, 0x58, 8 do
			local ok, tot = 0, 0
			for _, s in cs do
				local nup = b_u8(s.b, nupC)
				if nup >= 1 then
					tot += 1
					if o + nup * 16 <= s.bs and o + nup * 16 <= b_len(s.b) and tvalueOk(s.b, o, nup, tags) then ok += 1 end
				end
			end
			if tot == 0 or ok >= tot * 0.9 then cUp = o break end
		end
	end
	return {
		env = envOff,
		isC = isCOff,
		proto = protoOff,
		protoEnc = protoEnc,
		nup = nupC,
		stack = stackC,
		uprefs = upOff,
		cF = cF,
		cName = cName,
		cUp = cUp,
	}, protoTag, nupP, stackP, uvTag
end

local function deriveProto(sm, tags, known)
	local S = tags.string
	local function tsField(minFrac, exclude)
		local bestO, bestE, bestS = nil, nil, 0
		for o = 8, 0xF0, 8 do
			if o ~= exclude then
				for enc = 0, 4 do
					local hit, zero, used = 0, 0, 0
					for i, s in sm do
						if i > 120 then break end
						if o + 8 <= b_len(s.b) then
							used += 1
							local d = decodePtr(s.a + o, s.b, o, enc)
							if d == 0 then zero += 1 elseif tagAt(d, known) == S then hit += 1 end
						end
					end
					if used > 20 and hit >= used * minFrac and hit + zero >= used * 0.95 and hit > bestS then
						bestO, bestE, bestS = o, enc, hit
					end
				end
			end
		end
		return bestO, bestE
	end
	local srcOff, srcEnc = tsField(0.95, nil)
	if not srcOff then return nil, "proto source field not found" end
	local nameOff, nameEnc = tsField(0.05, srcOff)
	local ptrCands = {}
	for o = 8, 0xF0, 8 do
		if o ~= srcOff and o ~= nameOff then
			for enc = 0, 4 do
				local okc, nz, used = 0, 0, 0
				for i, s in sm do
					if i > 100 then break end
					if o + 8 <= b_len(s.b) then
						used += 1
						local d = decodePtr(s.a + o, s.b, o, enc)
						if d == 0 then okc += 1 elseif isptr(d) and tagAt(d, known) ~= S then okc += 1 nz += 1 end
					end
				end
				if used > 20 and okc >= used * 0.97 and nz >= math.max(4, used * 0.05) then
					ptrCands[#ptrCands + 1] = { o = o, enc = enc, dense = nz >= used * 0.2 }
				end
			end
		end
	end
	local cntCands = {}
	for c = 8, 0xF0 - 4, 4 do
		local ok, used = 0, 0
		for i, s in sm do
			if i > 100 then break end
			if c + 4 <= b_len(s.b) then
				used += 1
				local v = b_i32(s.b, c)
				if v >= 0 and v <= 100000 then ok += 1 end
			end
		end
		if used > 20 and ok == used then cntCands[#cntCands + 1] = c end
	end
	local kBest, pBest
	local ns = math.min(#sm, 80)
	for _, pc in ptrCands do
		local kLead, pLead, kStr = {}, {}, {}
		for i = 1, ns do
			local s = sm[i]
			local d = decodePtr(s.a + pc.o, s.b, pc.o, pc.enc)
			kLead[i], pLead[i], kStr[i] = 0, 0, 0
			if isptr(d) then
				local ab = rd(d, 64 * 16) or rd(d, 16 * 16) or rd(d, 64)
				if ab then
					local cap = b_len(ab) // 16
					local kl, ks = 0, 0
					while kl < cap and tvalueOk(ab, kl * 16, 1, tags) do
						if b_i32(ab, kl * 16 + 12) == S and tagAt(q(ab, kl * 16), known) == S then ks += 1 end
						kl += 1
					end
					kLead[i] = kl
					kStr[i] = ks
					local pl = 0
					local pcap = math.min(b_len(ab) // 8, 8)
					while pl < pcap and tagAt(q(ab, pl * 8), known) == s.tagP do pl += 1 end
					pLead[i] = pl
				end
			end
		end
		for _, c in cntCands do
			if not (c >= pc.o and c < pc.o + 8) then
				local kg, kb, ksum = 0, 0, 0
				local pg, pbad, psum = 0, 0, 0
				for i = 1, ns do
					local s = sm[i]
					local n = b_i32(s.b, c)
					if n > 0 then
						if kLead[i] >= math.min(n, 64) then
							if kStr[i] > 0 then
								kg += 1
								ksum += n
							end
						else
							kb += 1
						end
						if pLead[i] >= math.min(n, 8) then pg += 1 psum += n else pbad += 1 end
					end
				end
				if pc.dense and kg >= 8 and kb <= kg * 0.05 then
					if not kBest or kg > kBest.score or (kg == kBest.score and ksum > kBest.sum) then
						kBest = { o = pc.o, enc = pc.enc, c = c, score = kg, sum = ksum }
					end
				end
				if pg >= 4 and pbad <= pg * 0.05 then
					if not pBest or pg > pBest.score or (pg == pBest.score and psum > pBest.sum) then
						pBest = { o = pc.o, enc = pc.enc, c = c, score = pg, sum = psum }
					end
				end
			end
		end
	end
	return {
		source = srcOff,
		sourceEnc = srcEnc,
		name = nameOff,
		nameEnc = nameEnc,
		k = kBest and kBest.o,
		kEnc = kBest and kBest.enc,
		sizek = kBest and kBest.c,
		p = pBest and pBest.o,
		pEnc = pBest and pBest.enc,
		sizep = pBest and pBest.c,
	}
end

local function deriveProtoLine(protoSm, Pr)
	if not Pr.p or not Pr.sizep then return nil end
	local candidates = {}
	for c = 8, 0xF0 - 4, 4 do candidates[#candidates + 1] = c end
	local score = {}
	local parents = 0
	for i, s in protoSm do
		if parents >= 40 then break end
		local np = b_i32(s.b, Pr.sizep)
		if np >= 2 and np <= 200 then
			local arr = decodePtr(s.a + Pr.p, s.b, Pr.p, Pr.pEnc)
			local ab = rd(arr, math.min(np, 16) * 8)
			if ab then
				local kids = {}
				for e = 0, math.min(np, 16) - 1 do
					local kb = rd(q(ab, e * 8), 0xF0)
					if kb then kids[#kids + 1] = kb end
				end
				if #kids >= 2 then
					parents += 1
					for _, c in candidates do
						local mono = true
						local prev = -1
						local steps, ones = 0, 0
						local parentV = b_i32(s.b, c)
						for _, kb in kids do
							local v = b_i32(kb, c)
							if v < prev or v < 1 or v > 1000000 or v < parentV then mono = false break end
							if prev >= 0 then
								steps += 1
								if v - prev == 1 then ones += 1 end
							end
							prev = v
						end
						if mono and steps > 0 and ones * 2 < steps then
							local first = b_i32(kids[1], c)
							local last = b_i32(kids[#kids], c)
							if last > first then score[c] = (score[c] or 0) + 1 end
						end
					end
				end
			end
		end
	end
	local best, bs = nil, 0
	for c, v in score do
		if v > bs or (v == bs and best and c < best) then best, bs = c, v end
	end
	if best and bs >= parents * 0.7 and parents >= 5 then return best end
	return nil
end

local function deriveUpval(sm)
	for o = 8, 0x20, 8 do
		local selfRef, ok, used = 0, 0, 0
		for i, s in sm do
			if i > 200 then break end
			if o + 8 <= b_len(s.b) then
				used += 1
				local v = q(s.b, o)
				if isptr(v) then
					ok += 1
					if v > s.a and v < s.a + s.bs then selfRef += 1 end
				end
			end
		end
		if used > 10 and ok >= used * 0.95 and selfRef >= used * 0.2 then return { v = o } end
	end
	return nil
end

local function deriveUdata(sm, tags, known)
	local lenOff, dataOff
	local bestPass = -1
	for lo = 4, 12, 4 do
		for d = 0x10, 0x20, 8 do
			if d > lo + 3 then
				local pass, used = 0, 0
				for _, s in sm do
					used += 1
					local len = b_i32(s.b, lo)
					if len >= 0 and d + len <= s.bs and s.bs - (d + len) < 0x80 then pass += 1 end
				end
				if used > 10 and pass >= used * 0.99 then
					if d > (dataOff or 0) or (d == dataOff and lo < lenOff) then
						lenOff, dataOff, bestPass = lo, d, pass
					end
				end
			end
		end
	end
	if not lenOff then return nil, "userdata len/data not found" end
	local metaOff, metaEnc
	for o = 8, dataOff - 8, 8 do
		if not (lenOff >= o and lenOff < o + 8) then
			for enc = 0, 4 do
				local ok, nz, used = 0, 0, 0
				for i, s in sm do
					if i > 150 then break end
					used += 1
					local d = decodePtr(s.a + o, s.b, o, enc)
					if d == 0 then ok += 1 elseif tagAt(d, known) == tags.table then ok += 1 nz += 1 end
				end
				if used > 10 and ok >= used * 0.97 and nz >= 1 then metaOff, metaEnc = o, enc break end
			end
			if metaOff then break end
		end
	end
	local tagOff
	for b = 2, 7 do
		if not (b >= lenOff and b < lenOff + 4) then
			local vals = {}
			local distinct = 0
			for _, s in sm do
				local v = b_u8(s.b, b)
				if not vals[v] then vals[v] = true distinct += 1 end
			end
			if distinct >= 2 and distinct <= 64 and b ~= 2 then tagOff = b break end
		end
	end
	tagOff = tagOff or 3
	local groups = {}
	for _, s in sm do
		local key = b_u8(s.b, tagOff) * 100000 + math.max(0, b_i32(s.b, lenOff))
		local g = groups[key]
		if not g then g = {} groups[key] = g end
		g[#g + 1] = s
	end
	local instTag, instOff, instLen
	local bestHits = 0
	local instGroups = {}
	for key, g in groups do
		if #g >= 8 then
			local len = key % 100000
			local tagv = key // 100000
			for inner = 0, math.min(len, 32) - 8, 8 do
				local hits = 0
				for i, s in g do
					if i > 24 then break end
					local off = dataOff + inner
					if off + 8 <= b_len(s.b) and looksInstance(q(s.b, off)) then hits += 1 end
				end
				if hits >= math.min(#g, 24) * 0.9 then
					if instGroups[tagv] == nil then instGroups[tagv] = inner end
					if hits > bestHits then
						instTag, instOff, instLen, bestHits = tagv, inner, len, hits
					end
				end
			end
		end
	end
	return {
		tag = tagOff,
		len = lenOff,
		data = dataOff,
		meta = metaOff,
		metaEnc = metaEnc or 0,
		instTag = instTag,
		instOff = instOff,
		instLen = instLen,
		instGroups = instGroups,
	}
end

local function deriveThread(sm, tags, known, lGlobal)
	local gtOff
	for o = 8, 0x100 - 8, 8 do
		if o ~= lGlobal then
			local ok, used = 0, 0
			for i, s in sm do
				if i > 100 then break end
				if o + 8 <= b_len(s.b) then
					used += 1
					if tagAt(q(s.b, o), known) == tags.table then ok += 1 end
				end
			end
			if used > 5 and ok >= used * 0.9 then gtOff = o break end
		end
	end
	local exOff, scOff, best = nil, nil, 0
	for o = 8, 0x100 - 8, 8 do
		if o ~= lGlobal and o ~= gtOff then
			local cnt, firstInst = {}, {}
			local used = 0
			for _, s in sm do
				if used >= 30 then break end
				if o + 8 <= b_len(s.b) then
					local e = q(s.b, o)
					if isptr(e) and not moduleRange(e) then
						local eb = rd(e, 0x100)
						if eb then
							used += 1
							for so = 0, 0x100 - 8, 8 do
								local ia = q(eb, so)
								if looksInstance(ia) then
									cnt[so] = (cnt[so] or 0) + 1
									firstInst[so] = firstInst[so] or ia
								end
							end
						end
					end
				end
			end
			for so, c in cnt do
				if used >= 5 and c >= used * 0.6 then
					local bonus = 0
					local cls = instanceClass(firstInst[so])
					if cls == "Script" or cls == "LocalScript" or cls == "ModuleScript" or cls == "CoreScript" then bonus = 1000 end
					if c + bonus > best then exOff, scOff, best = o, so, c + bonus end
				end
			end
		end
	end
	return { gt = gtOff, extra = exOff, extraScript = scOff }
end

local function deriveGlobals(vms)
	local votes = {}
	for _, vm in vms do
		local gb = rd(vm.G, 0x200)
		if gb then
			for o = 0, 0x200 - 16, 8 do
				local x, y = q(gb, o), q(gb, o + 8)
				if x > 262144 and y > 262144 and x < 0x4000000000 and y < 0x4000000000 and x >= y and x <= y * 4 then
					votes[o] = (votes[o] or 0) + 1
				end
			end
		end
	end
	local best, bv = nil, 0
	for o, v in votes do
		if v > bv or (v == bv and o < best) then best, bv = o, v end
	end
	if not best then return {} end
	return { threshold = best, totalbytes = best + 8 }
end

local function sourceKind(text)
	if not text then return "unknown" end
	if string.find(text, "^[=@]?CoreGui") or string.find(text, "^[=@]?CorePackages") or string.find(text, "^[=@]?CoreScripts") or string.find(text, "^[=@]?RobloxGui") or string.find(text, "^[=@]?BuiltInPlugins") then
		return "core"
	end
	return "game"
end

local tsRead

local function classifyVM(vm, maxPages)
	local core, game, total = 0, 0, 0
	local Pr = Layout.proto
	local P = Layout.pages
	local PT = Layout.tags.proto
	local ctx = newCtx({})
	local pages = listPages(vm, "gc", ctx)
	vm.gcPages = #pages
	local stride = math.max(1, #pages / (maxPages or 200))
	local seenSrc = {}
	vm.sources = {}
	vm.protoSamples = {}
	local idx = 1
	while idx <= #pages and total < 400 do
		local e = pages[math.floor(idx)]
		idx += stride
		local pg, pgs, bsz = e[1], e[2], e[3]
		if pgs <= 0x10000 and bsz >= Pr.source + 8 then
			local buf = rd(pg, pgs)
			local at, stop
			if buf then at, stop = pageRange(buf, P, pgs, bsz) end
			if at then
				while at + bsz <= stop do
					if b_u8(buf, at + 1) == PT then
						if #vm.protoSamples < 300 then
							local span = math.min(bsz, 0x100, b_len(buf) - at)
							local sb = b_create(span)
							b_copy(sb, 0, buf, at, span)
							vm.protoSamples[#vm.protoSamples + 1] = { a = pg + at, b = sb, bs = bsz }
						end
						local d = decodePtr(pg + at + Pr.source, buf, at + Pr.source, Pr.sourceEnc)
						local text = seenSrc[d]
						if text == nil then
							text = tsRead(d, 8192) or false
							seenSrc[d] = text
							if text and #vm.sources < 6 then vm.sources[#vm.sources + 1] = string.sub(text, 1, 80) end
						end
						if text then
							total += 1
							if sourceKind(text) == "core" then core += 1 else game += 1 end
						end
					end
					at += bsz
				end
			end
		end
		if not step(ctx) then break end
	end
	vm.coreProtos, vm.gameProtos = core, game
	if total == 0 then vm.kind = "unknown"
	elseif core >= total * 0.6 then vm.kind = "core"
	else vm.kind = "game" end
	return vm.kind
end

local function vmStats(vm)
	local gl = Layout and Layout.globals or {}
	local gb = rd(vm.G, 0x200)
	if gb then
		vm.strings = b_u32(gb, vm.strt + 8)
		if gl.totalbytes then vm.bytes = q(gb, gl.totalbytes) end
	end
end

local TextByAddr = {}
local TextByAddrN = 0
local AddrByText = {}

tsRead = function(p, maxLen)
	if not isptr(p) then return nil end
	maxLen = maxLen or 0x100000
	local St = Layout.str
	local hb = rd(p, St.data + 0x40)
	if not hb then
		hb = rd(p, St.data)
		if not hb then return nil end
	end
	if b_u8(hb, 1) ~= Layout.tags.string then return nil end
	local len = b_u32(hb, St.len)
	if len > maxLen then return nil end
	if St.data + len <= b_len(hb) then return b_str(hb, St.data, len) end
	local db = rd(p + St.data, len)
	if not db then return nil end
	return b_str(db, 0, len)
end

local function tsCached(p)
	local e = TextByAddr[p]
	local St = Layout.str
	if e then
		local hb = rd(p, St.data)
		if hb and b_u8(hb, 1) == Layout.tags.string and b_u32(hb, St.hash) == e.h and b_u32(hb, St.len) == #e.s then
			return e.s
		end
		TextByAddr[p] = nil
	end
	local hb = rd(p, St.data)
	if not hb then return nil end
	local s = tsRead(p)
	if s then
		if TextByAddrN > 20000 then TextByAddr = {} TextByAddrN = 0 end
		TextByAddr[p] = { s = s, h = b_u32(hb, St.hash) }
		TextByAddrN += 1
	end
	return s
end

local function vmKey(vm)
	return vm.G
end

local function cachedIntern(vm, text)
	local m = AddrByText[vmKey(vm)]
	if not m then return nil end
	local p = m[text]
	if not p then return nil end
	if tsRead(p, #text) == text then return p end
	m[text] = nil
	return nil
end

local function rememberIntern(vm, text, p)
	local k = vmKey(vm)
	local m = AddrByText[k]
	if not m then m = {} AddrByText[k] = m end
	m[text] = p
end

local function resolveStrings(vm, needles, ctx)
	local out, pending, byLen = {}, 0, {}
	for _, s in needles do
		if type(s) == "string" and out[s] == nil then
			local c = cachedIntern(vm, s)
			if c then
				out[s] = c
			else
				out[s] = false
				pending += 1
				local l = byLen[#s]
				if not l then l = {} byLen[#s] = l end
				l[#l + 1] = s
			end
		end
	end
	if pending == 0 then return out end
	local St = Layout.str
	local S = Layout.tags.string
	forEachObject(vm, { [S] = true }, function(addr, tt, buf, at, bsz)
		local len = b_u32(buf, at + St.len)
		local l = byLen[len]
		if l then
			local text
			if at + St.data + len <= b_len(buf) then text = b_str(buf, at + St.data, len) else text = tsRead(addr) end
			for _, s in l do
				if out[s] == false and text == s then
					out[s] = addr
					rememberIntern(vm, s, addr)
					pending -= 1
				end
			end
			if pending <= 0 then return true end
		end
		return false
	end, ctx or newCtx())
	return out
end

local ProxyInfo = setmetatable({}, { __mode = "k" })
local ProxyCache = setmetatable({}, { __mode = "v" })

local TableMeta, FunctionMeta, ObjectMeta = {}, {}, {}
local LightMeta = {}

local wrap
local decodeTV

local function makeVector(x, y, z)
	if vector and vector.create then return vector.create(x, y, z) end
	if Vector3 then return Vector3.new(x, y, z) end
	return { X = x, Y = y, Z = z }
end

local function kindOfTag(tt)
	local T = Layout.tags
	if tt == T.table then return "table" end
	if tt == T.func then return "function" end
	if tt == T.userdata then return "userdata" end
	if tt == T.thread then return "thread" end
	if tt == rawget(T, "proto") then return "proto" end
	if tt == rawget(T, "upval") then return "upvalue" end
	if tt == T.string then return "string" end
	return "object"
end

local InstanceUdata = setmetatable({}, { __mode = "k" })

local function instOffFor(tag)
	local U = Layout.udata
	if not U then return nil end
	if U.instGroups and U.instGroups[tag] then return U.instGroups[tag] end
	if U.instTag and tag == U.instTag then return U.instOff end
	return nil
end

local function instReadSpan()
	local U = Layout.udata
	local m = U.instOff or 0
	if U.instGroups then
		for _, off in U.instGroups do
			if off > m then m = off end
		end
	end
	return U.data + m + 8
end

local function udataInstanceAddr(u, buf, at)
	local U = Layout.udata
	if not U then return nil end
	if not buf then
		buf = rd(u, instReadSpan())
		at = 0
		if not buf then return nil end
	end
	if at + U.tag + 1 > b_len(buf) then return nil end
	local off = instOffFor(b_u8(buf, at + U.tag))
	if not off or at + U.data + off + 8 > b_len(buf) then return nil end
	local ia = q(buf, at + U.data + off)
	if looksInstance(ia) then return ia end
	return nil
end

local function instanceFromUdata(p, vm)
	if not Layout.udata or not toUserdata then return nil end
	local ia = udataInstanceAddr(p)
	if not ia then return nil end
	local ok, inst = pcall(toUserdata, ia)
	if ok and inst then
		pcall(function() InstanceUdata[inst] = { udata = p, inst = ia, vm = vm or Current } end)
		return inst, ia
	end
	return nil
end

wrap = function(p, tt, vm)
	if not isptr(p) or type(tt) ~= "number" then return nil end
	vm = vm or Current
	local key = p
	local px = ProxyCache[key]
	if px then
		local inf = ProxyInfo[px]
		if inf and inf.tag == tt and inf.vm == vm then return px end
	end
	local kind = kindOfTag(tt)
	if kind == "userdata" and SevereGC.InstanceConversion ~= false then
		local inst = instanceFromUdata(p, vm)
		if inst then return inst end
	end
	local mt
	if kind == "table" then mt = TableMeta
	elseif kind == "function" then mt = FunctionMeta
	else mt = ObjectMeta end
	px = setmetatable({}, mt)
	ProxyInfo[px] = { addr = p, tag = tt, kind = kind, vm = vm or Current }
	ProxyCache[key] = px
	return px
end

decodeTV = function(b, o, vm)
	local T = Layout.tags
	local tt = b_i32(b, o + 12)
	if tt == 0 then return nil end
	if tt == T.boolean then return b_u32(b, o) ~= 0 end
	if tt == T.number then return b_f64(b, o) end
	if tt == T.vector then return makeVector(b_f32(b, o), b_f32(b, o + 4), b_f32(b, o + 8)) end
	local p = q(b, o)
	if tt == T.string then return tsRead(p) end
	if tt == T.lightuserdata then
		local lp = setmetatable({}, LightMeta)
		ProxyInfo[lp] = { addr = b_u32(b, o) + b_u32(b, o + 4) * TWO32, tag = tt, kind = "lightuserdata" }
		return lp
	end
	return wrap(p, tt, vm)
end

local function infoOf(v)
	return type(v) == "table" and ProxyInfo[v] or nil
end

local function vmOf(x)
	local inf = infoOf(x)
	return (inf and inf.vm) or Current
end

local function readTableHeader(t)
	if not Layout then error("SevereGC: detached; call SevereGC.attach() first", 3) end
	local Tb = Layout.table
	local b = rd(t, Tb.span)
	if not b then return nil end
	if b_u8(b, 1) ~= Layout.tags.table then return nil end
	local h = {
		lsz = b_u8(b, Tb.lsz),
		node = q(b, Tb.node),
		meta = Tb.meta and q(b, Tb.meta) or 0,
		sizearray = Tb.sizearray and b_i32(b, Tb.sizearray) or 0,
		array = Tb.array and decodePtr(t + Tb.array, b, Tb.array, Tb.arrayEnc) or 0,
	}
	if h.sizearray < 0 or h.sizearray > 0x4000000 then h.sizearray = 0 end
	if not isptr(h.array) then h.sizearray = 0 end
	return h
end

local function readNodes(h)
	if h.node == Layout.table.dummy or not isptr(h.node) then return nil, 0 end
	local n = 2 ^ h.lsz
	if n > 0x20000 then return nil, 0 end
	local nb = rd(h.node, n * 32)
	return nb, n
end

local function prepareKey(key, vm)
	local tk = type(key)
	if tk == "string" then
		return { kind = "s", text = key, ptr = cachedIntern(vm, key) }
	elseif tk == "number" then
		return { kind = "n", value = key }
	elseif tk == "boolean" then
		return { kind = "b", value = key }
	end
	local inf = infoOf(key)
	if inf then return { kind = "p", addr = inf.addr, tag = inf.tag } end
	return nil
end

local function nodeKeyMatches(nb, i, k, vm)
	local T = Layout.tags
	local base = i * 32
	local ktt = band(b_u32(nb, base + 28), 15)
	if k.kind == "s" then
		if ktt ~= band(T.string, 15) then return false end
		local kp = q(nb, base + 16)
		if k.ptr then return kp == k.ptr end
		local s = tsCached(kp)
		if s == k.text then
			k.ptr = kp
			rememberIntern(vm, k.text, kp)
			return true
		end
		return false
	elseif k.kind == "n" then
		return ktt == band(T.number, 15) and b_f64(nb, base + 16) == k.value
	elseif k.kind == "b" then
		return ktt == band(T.boolean, 15) and ((b_u32(nb, base + 16) ~= 0) == k.value)
	elseif k.kind == "p" then
		return type(k.tag) == "number" and ktt == band(k.tag, 15) and q(nb, base + 16) == k.addr
	end
	return false
end

local function decodeHash(sv, f, enc)
	if enc == "add" then return (sv + f) % TWO32 end
	if enc == "xor" then return bxor(sv, f) end
	if enc == "ssub" then return (sv - f) % TWO32 end
	if enc == "fsub" then return (f - sv) % TWO32 end
	return sv
end

local function stringHash(p)
	local St = Layout.str
	local enc = St and St.hashEnc
	if not enc then return nil end
	local hb = rd(p + St.hash, 4)
	if not hb then return nil end
	return decodeHash(b_u32(hb, 0), (p + St.hash) % TWO32, enc)
end

local function probeNode(node, lsz, kp, h)
	local size = 2 ^ lsz
	local i = band(h, size - 1)
	local s15 = band(Layout.tags.string, 15)
	for _ = 1, 64 do
		local nb = rd(node + i * 32, 32)
		if not nb then return nil end
		local w = b_u32(nb, 28)
		if band(w, 15) == s15 and q(nb, 16) == kp then return node + i * 32, nb end
		local nx = w // 16
		if nx >= 0x8000000 then nx -= 0x10000000 end
		if nx == 0 then return false end
		i += nx
		if i < 0 or i >= size then return false end
	end
	return false
end

local MemoTables = {}
local MemoCount = 0

local function memoGet(t, keyId)
	local m = MemoTables[t]
	return m and m[keyId]
end

local function memoSet(t, keyId, slot)
	local m = MemoTables[t]
	if not m then
		if MemoCount > 8192 then MemoTables = {} MemoCount = 0 end
		m = {}
		MemoTables[t] = m
		MemoCount += 1
	end
	m[keyId] = slot
end

local function keyId(key)
	local tk = type(key)
	if tk == "string" then return "s" .. key end
	if tk == "number" then return "n" .. tostring(key) end
	if tk == "boolean" then return key and "bt" or "bf" end
	local inf = infoOf(key)
	if inf then return "p" .. tostring(inf.addr) end
	return nil
end

local function findSlot(t, key, vm)
	local h = readTableHeader(t)
	if not h then return nil, "not a live table" end
	if type(key) == "number" and key >= 1 and key <= h.sizearray and key % 1 == 0 then
		return h.array + (key - 1) * 16, h
	end
	local id = keyId(key)
	local k = prepareKey(key, vm)
	if not k then return nil, "unsupported key type" end
	local memo = id and memoGet(t, id)
	if memo and memo.node == h.node then
		local nb1 = rd(h.node + memo.index * 32, 32)
		if nb1 and nodeKeyMatches(nb1, 0, k, vm) then return h.node + memo.index * 32, h end
	end
	if k.kind == "s" and k.ptr and h.lsz >= 6 and h.lsz <= 17 and h.node ~= Layout.table.dummy and isptr(h.node) then
		local hh = stringHash(k.ptr)
		if hh then
			local slot = probeNode(h.node, h.lsz, k.ptr, hh)
			if slot then
				if id then memoSet(t, id, { node = h.node, index = (slot - h.node) // 32 }) end
				return slot, h
			elseif slot == false then
				return nil, h
			end
		end
	end
	local nb, n = readNodes(h)
	if not nb then return nil, h end
	for i = 0, n - 1 do
		if nodeKeyMatches(nb, i, k, vm) then
			if id then memoSet(t, id, { node = h.node, index = i }) end
			return h.node + i * 32, h
		end
	end
	return nil, h
end

local function tableGet(t, key, vm)
	local slot = findSlot(t, key, vm)
	if not slot then return nil end
	local vb = rd(slot, 16)
	if not vb then return nil end
	return decodeTV(vb, 0, vm)
end

local function pinString(p)
	if not memWrite then return end
	local m = rd(p, 2)
	if not m or b_u8(m, 1) ~= Layout.tags.string then return end
	local v = b_u8(m, 0)
	local nv = band(v, 0xFC)
	if nv ~= v then
		local w = b_create(1)
		buffer.writeu8(w, 0, nv)
		pcall(memWrite, p, w)
	end
end

local function udataOfInstance(inst, vm)
	vm = vm or Current
	local iu = InstanceUdata[inst]
	if iu and iu.vm == vm then
		local hb = rd(iu.udata, 8)
		if hb and b_u8(hb, 1) == Layout.tags.userdata and udataInstanceAddr(iu.udata) == iu.inst then return iu.udata end
	end
	local ia = instAddr(inst)
	if not ia or not Layout.udata then return nil end
	local found
	forEachObject(vm, { [Layout.tags.userdata] = true }, function(addr, tt, buf, at)
		if udataInstanceAddr(addr, buf, at) == ia then
			found = addr
			return true
		end
		return false
	end, newCtx())
	if found then pcall(function() InstanceUdata[inst] = { udata = found, inst = ia, vm = vm } end) end
	return found
end

local function putPtr(b, p, tag)
	b_wu32(b, 0, p % TWO32)
	b_wu32(b, 4, p // TWO32)
	b_wi32(b, 12, tag)
end

local function encodeTV(v, vm)
	local T = Layout.tags
	local b = b_create(16)
	local tv = type(v)
	if v == nil then
		b_wi32(b, 12, 0)
	elseif tv == "boolean" then
		b_wu32(b, 0, v and 1 or 0)
		b_wi32(b, 12, T.boolean)
	elseif tv == "number" then
		b_wf64(b, 0, v)
		b_wi32(b, 12, T.number)
	elseif tv == "vector" or (tv == "userdata" and typeof and typeof(v) == "Vector3") then
		b_wf32(b, 0, v.X or v.x)
		b_wf32(b, 4, v.Y or v.y)
		b_wf32(b, 8, v.Z or v.z)
		b_wi32(b, 12, T.vector)
	elseif tv == "string" then
		local r = resolveStrings(vm, { v })
		local p = r[v]
		if not p then error("SevereGC: the string '" .. v .. "' does not exist in the target VM, so it cannot be written", 3) end
		pinString(p)
		putPtr(b, p, T.string)
	else
		if isInstanceValue(v) then
			local u = udataOfInstance(v, vm)
			if not u then error("SevereGC: that Instance has no userdata in the target VM (no script there references it), so it cannot be written", 3) end
			putPtr(b, u, T.userdata)
			return b
		end
		local inf = infoOf(v)
		if not inf or not (inf.kind == "table" or inf.kind == "function" or inf.kind == "userdata" or inf.kind == "thread" or inf.kind == "lightuserdata") then
			error("SevereGC: cannot write a value of type " .. ((inf and inf.kind) or tv), 3)
		end
		if inf.kind == "lightuserdata" then
			putPtr(b, inf.addr, T.lightuserdata)
			return b
		end
		if inf.vm and vm and inf.vm ~= vm then error("SevereGC: cannot write a reference from another VM", 3) end
		local hb = rd(inf.addr, 8)
		if not hb or b_u8(hb, 1) ~= inf.tag then error("SevereGC: that object no longer exists", 3) end
		putPtr(b, inf.addr, inf.tag)
	end
	return b
end

local function writeSlotKnown(slot, oldtt, b)
	if not memWrite then error("SevereGC: memory.writebuffer is not available", 3) end
	local T = Layout.tags
	local newtt = b_i32(b, 12)
	local payload = b_create(12)
	b_copy(payload, 0, b, 0, 12)
	local function put(addr, buf)
		local ok, err = pcall(memWrite, addr, buf)
		if not ok then error("SevereGC: write failed: " .. tostring(err), 4) end
	end
	if oldtt == newtt then
		put(slot, payload)
	else
		if oldtt >= T.string then
			local tb = b_create(4)
			b_wi32(tb, 0, T.number)
			put(slot + 12, tb)
		end
		put(slot, payload)
		local tb2 = b_create(4)
		b_wi32(tb2, 0, newtt)
		put(slot + 12, tb2)
	end
	return true
end

local function writeSlot(slot, b)
	if not memWrite then error("SevereGC: memory.writebuffer is not available", 3) end
	local cur = rd(slot, 16)
	if not cur then error("SevereGC: the slot is not readable", 3) end
	return writeSlotKnown(slot, b_i32(cur, 12), b)
end

local function tableSet(t, key, v, vm)
	local b = encodeTV(v, vm)
	local slot, h = findSlot(t, key, vm)
	if not slot then
		error("SevereGC: key " .. tostring(key) .. " does not exist in this table; only existing keys can be written", 3)
	end
	local h2 = readTableHeader(t)
	if not h2 or h2.node ~= h.node or h2.lsz ~= h.lsz or h2.array ~= h.array or h2.sizearray ~= h.sizearray then
		error("SevereGC: the table changed while writing; try again", 3)
	end
	return writeSlot(slot, b)
end

local function tableEntries(t, vm, limit)
	local out = {}
	local h = readTableHeader(t)
	if not h then return out end
	limit = limit or math.huge
	if h.sizearray > 0 then
		local n = math.min(h.sizearray, 0x10000)
		local ab = rd(h.array, n * 16)
		if ab then
			for i = 0, n - 1 do
				if b_i32(ab, i * 16 + 12) ~= 0 then
					out[#out + 1] = { i + 1, decodeTV(ab, i * 16, vm) }
					if #out >= limit then return out end
				end
			end
		end
	end
	local nb, n = readNodes(h)
	if nb then
		local T = Layout.tags
		for i = 0, n - 1 do
			local base = i * 32
			if b_i32(nb, base + 12) ~= 0 then
				local ktt = band(b_u32(nb, base + 28), 15)
				if ktt ~= 0 then
					local key
					if ktt == band(T.string, 15) then
						key = tsCached(q(nb, base + 16))
					else
						local kb = b_create(16)
						b_copy(kb, 0, nb, base + 16, 12)
						b_wi32(kb, 12, ktt)
						key = decodeTV(kb, 0, vm)
					end
					if key ~= nil then
						out[#out + 1] = { key, decodeTV(nb, base, vm) }
						if #out >= limit then return out end
					end
				end
			end
		end
	end
	return out
end

TableMeta.__index = function(px, key)
	local inf = ProxyInfo[px]
	return tableGet(inf.addr, key, inf.vm)
end

TableMeta.__newindex = function(px, key, v)
	local inf = ProxyInfo[px]
	tableSet(inf.addr, key, v, inf.vm)
end

TableMeta.__iter = function(px)
	local inf = ProxyInfo[px]
	local list = tableEntries(inf.addr, inf.vm)
	local i = 0
	return function()
		i += 1
		local e = list[i]
		if e then return e[1], e[2] end
		return nil
	end
end

TableMeta.__len = function(px)
	local inf = ProxyInfo[px]
	local h = readTableHeader(inf.addr)
	if not h or h.sizearray == 0 then return 0 end
	local n = math.min(h.sizearray, 0x10000)
	local ab = rd(h.array, n * 16)
	if not ab then return 0 end
	local c = 0
	for i = 0, n - 1 do
		if b_i32(ab, i * 16 + 12) == 0 then break end
		c = i + 1
	end
	return c
end

TableMeta.__tostring = function(px)
	return string.format("table: 0x%x (remote)", ProxyInfo[px].addr)
end

FunctionMeta.__tostring = function(px)
	return string.format("function: 0x%x (remote)", ProxyInfo[px].addr)
end

FunctionMeta.__call = function()
	error("SevereGC: remote functions live inside Roblox and cannot be called from Severe", 2)
end

FunctionMeta.__index = function(px, k)
	return SevereGC[k] and function(_, ...) return SevereGC[k](px, ...) end or nil
end

ObjectMeta.__tostring = function(px)
	local inf = ProxyInfo[px]
	return string.format("%s: 0x%x (remote)", inf.kind, inf.addr)
end

LightMeta.__tostring = function(px)
	return string.format("lightuserdata: 0x%x", ProxyInfo[px].addr)
end

local function requireAttached()
	if not Layout or not Current then
		local ok, err = SevereGC.attach()
		if not ok then error("SevereGC: not attached: " .. tostring(err), 3) end
	end
end

local function addrOf(x, kind)
	local inf = infoOf(x)
	if inf then return inf.addr, inf end
	if type(x) == "number" then return x, nil end
	error("SevereGC: expected a remote " .. (kind or "object") .. ", got " .. (typeof and typeof(x) or type(x)), 3)
end

local function closureInfo(f, soft)
	ensureLazy("functions")
	if not Layout then error("SevereGC: detached; call SevereGC.attach() first", 3) end
	local C = Layout.closure
	local a = addrOf(f, "function")
	local span = math.max(C.uprefs, C.cUp or 0, C.cName or 0, C.cF or 0, C.env, C.proto) + 8
	local b = rd(a, span)
	if not b or b_u8(b, 1) ~= Layout.tags.func then
		if soft then return nil end
		error("SevereGC: that function no longer exists (it was garbage collected)", 3)
	end
	local isC = b_u8(b, C.isC) == 1
	local nup = b_u8(b, C.nup)
	local proto = 0
	if not isC then proto = decodePtr(a + C.proto, b, C.proto, C.protoEnc) end
	return a, isC, nup, proto, b
end

local function protoOf(x, soft)
	ensureLazy("functions")
	local inf = infoOf(x)
	if inf and inf.kind == "proto" then
		local hb = rd(inf.addr, 8)
		if not hb or b_u8(hb, 1) ~= Layout.tags.proto then
			if soft then return nil end
			error("SevereGC: that proto no longer exists", 3)
		end
		return inf.addr
	end
	local a, isC, _, proto = closureInfo(x, soft)
	if not a or isC then return nil end
	return proto
end

local function protoField(p, off, enc)
	local b = rd(p + off, 8)
	if not b then return 0 end
	return decodePtr(p + off, b, 0, enc)
end

local function protoInt(p, off)
	if not off then return nil end
	local b = rd(p + off, 4)
	return b and b_i32(b, 0) or nil
end

function SevereGC.getinfo(f)
	ensureLazy("functions")
	requireAttached()
	local inf = infoOf(f)
	local out = { func = f }
	local p
	if inf and inf.kind == "proto" then
		p = protoOf(f, true)
		if not p then return nil end
		out.what = "Lua"
	else
		local a, isC, nup, proto, b = closureInfo(f, true)
		if not a then return nil end
		out.nups = nup
		out.address = a
		if isC then
			out.what = "C"
			out.source = "=[C]"
			out.short_src = "[C]"
			local C = Layout.closure
			if C.cName then out.name = tsRead(readPtrAt(a + C.cName, 0), 256) end
			if C.cF then out.cfunction = readPtrAt(a + C.cF, 0) end
			return out
		end
		out.what = "Lua"
		p = proto
	end
	local Pr = Layout.proto
	local pb = rd(p, 0xF0)
	if not pb then return out end
	out.proto = p
	out.source = tsRead(decodePtr(p + Pr.source, pb, Pr.source, Pr.sourceEnc), 4096)
	if out.source then
		out.short_src = (string.gsub(out.source, "^[=@]", ""))
	end
	if Pr.name then out.name = tsRead(decodePtr(p + Pr.name, pb, Pr.name, Pr.nameEnc), 512) end
	if Pr.nups then out.nups = b_u8(pb, Pr.nups) end
	if Pr.maxstack then out.maxstacksize = b_u8(pb, Pr.maxstack) end
	if Pr.line then out.linedefined = b_i32(pb, Pr.line) end
	if Pr.sizek then out.sizek = b_i32(pb, Pr.sizek) end
	if Pr.sizep then out.sizep = b_i32(pb, Pr.sizep) end
	return out
end

local function upvalueSlots(f, soft)
	ensureLazy("functions")
	local a, isC, nup, _, b = closureInfo(f, soft)
	if not a then return nil, {}, 0, {} end
	local C = Layout.closure
	local base
	if isC then base = C.cUp else base = C.uprefs end
	if not base or nup == 0 then return a, {}, nup, {} end
	local ub = rd(a + base, nup * 16)
	local slots, open = {}, {}
	if not ub then return a, slots, nup, open end
	local T = Layout.tags
	local U = T.upval
	for i = 0, nup - 1 do
		local tt = b_i32(ub, i * 16 + 12)
		local slot = a + base + i * 16
		if U and tt == U then
			slot = false
			if Layout.upval then
				local uv = q(ub, i * 16)
				local vp = readPtrAt(uv + Layout.upval.v, 0)
				if isptr(vp) then
					slot = vp
					open[i + 1] = not (vp > uv and vp < uv + 0x40)
				end
			end
		elseif tt == T.proto then
			slot = false
		end
		slots[i + 1] = slot
	end
	return a, slots, nup, open
end

function SevereGC.getupvalues(f)
	requireAttached()
	local _, slots, nup = upvalueSlots(f, true)
	local vm = vmOf(f)
	local out = {}
	for i = 1, nup do
		local slot = slots[i]
		if slot then
			local vb = rd(slot, 16)
			if vb then out[i] = decodeTV(vb, 0, vm) end
		end
	end
	return out
end

function SevereGC.getupvalue(f, i)
	requireAttached()
	local a, slots, nup = upvalueSlots(f, true)
	if not a then return nil end
	if i < 1 or i > nup then error("SevereGC: upvalue index out of range", 2) end
	local slot = slots[i]
	if not slot then return nil end
	local vb = rd(slot, 16)
	if not vb then return nil end
	return decodeTV(vb, 0, vmOf(f))
end

function SevereGC.setupvalue(f, i, v)
	requireAttached()
	local b = encodeTV(v, vmOf(f))
	local _, slots, nup, open = upvalueSlots(f)
	if i < 1 or i > nup then error("SevereGC: upvalue index out of range", 2) end
	local slot = slots[i]
	if not slot then error("SevereGC: upvalue " .. i .. " could not be resolved", 2) end
	if open[i] then
		local _, again = upvalueSlots(f)
		if again[i] ~= slot then error("SevereGC: the upvalue moved while writing; try again", 2) end
	end
	return writeSlot(slot, b)
end

local function constantsOf(p)
	ensureLazy("functions")
	local Pr = Layout.proto
	if not Pr.k or not Pr.sizek then error("SevereGC: constant layout was not derived", 3) end
	local n = protoInt(p, Pr.sizek) or 0
	if n <= 0 then return 0, 0 end
	local k = protoField(p, Pr.k, Pr.kEnc)
	return k, math.min(n, 0x10000)
end

function SevereGC.getconstants(f)
	requireAttached()
	local p = protoOf(f, true)
	if not p then return {} end
	local k, n = constantsOf(p)
	local out = {}
	if n == 0 then return out end
	local kb = rd(k, n * 16)
	if not kb then return out end
	local vm = vmOf(f)
	for i = 0, n - 1 do out[i + 1] = decodeTV(kb, i * 16, vm) end
	return out
end

function SevereGC.getconstant(f, i)
	requireAttached()
	local p = protoOf(f, true)
	if not p then return nil end
	local k, n = constantsOf(p)
	if i < 1 or i > n then return nil end
	local kb = rd(k + (i - 1) * 16, 16)
	if not kb then return nil end
	return decodeTV(kb, 0, vmOf(f))
end

function SevereGC.setconstant(f, i, v)
	requireAttached()
	local b = encodeTV(v, vmOf(f))
	local p = protoOf(f)
	if not p then error("SevereGC: C functions have no constants", 2) end
	local k, n = constantsOf(p)
	if i < 1 or i > n then error("SevereGC: constant index out of range", 2) end
	return writeSlot(k + (i - 1) * 16, b)
end

function SevereGC.getprotos(f)
	ensureLazy("functions")
	requireAttached()
	local p = protoOf(f, true)
	local out = {}
	if not p then return out end
	local Pr = Layout.proto
	if not Pr.p or not Pr.sizep then return out end
	local n = math.min(protoInt(p, Pr.sizep) or 0, 0x10000)
	if n <= 0 then return out end
	local arr = protoField(p, Pr.p, Pr.pEnc)
	local ab = rd(arr, n * 8)
	if not ab then return out end
	local vm = vmOf(f)
	for i = 0, n - 1 do
		out[i + 1] = wrap(q(ab, i * 8), Layout.tags.proto, vm)
	end
	return out
end

function SevereGC.getproto(f, i, activated)
	local list = SevereGC.getprotos(f)
	local pr = list[i]
	if not pr then return nil end
	if activated then return SevereGC.getclosures(pr) end
	return pr
end

function SevereGC.getenv(f)
	ensureLazy("functions")
	requireAttached()
	local a = addrOf(f, "function")
	local C = Layout.closure
	local e = readPtrAt(a + C.env, 0)
	return wrap(e, Layout.tags.table, vmOf(f))
end
SevereGC.getfenv = SevereGC.getenv

function SevereGC.getmetatable(t, opts)
	requireAttached()
	if isInstanceValue(t) then
		local U = Layout.udata
		if not U or not U.meta then return nil end
		local vm = pickVM(opts)
		local u = udataOfInstance(t, vm)
		if not u then return nil end
		return wrap(readPtrAt(u + U.meta, U.metaEnc), Layout.tags.table, vm)
	end
	local a, inf = addrOf(t, "table")
	if inf and inf.kind == "userdata" then
		local U = Layout.udata
		if not U or not U.meta then return nil end
		local m = readPtrAt(a + U.meta, U.metaEnc)
		return wrap(m, Layout.tags.table, vmOf(t))
	end
	local h = readTableHeader(a)
	if not h or h.meta == 0 then return nil end
	return wrap(h.meta, Layout.tags.table, vmOf(t))
end

function SevereGC.rawget(t, k)
	requireAttached()
	local a, inf = addrOf(t, "table")
	return tableGet(a, k, (inf and inf.vm) or Current)
end

function SevereGC.rawset(t, k, v)
	requireAttached()
	local a, inf = addrOf(t, "table")
	return tableSet(a, k, v, (inf and inf.vm) or Current)
end

local function keyBytes(buf, at)
	return b_str(buf, at + 16, 12) .. string.char(band(b_u32(buf, at + 28), 15))
end

local function slotsOf(t, keys, vm)
	local h = readTableHeader(t)
	if not h then return nil end
	local slots = {}
	local nb, n
	if h.node ~= Layout.table.dummy and isptr(h.node) and h.lsz <= 8 then nb, n = readNodes(h) end
	local byPtr, byText = {}, {}
	local textLeft, anyStr = 0, false
	if nb then
		for _, key in keys do
			if type(key) == "string" then
				anyStr = true
				local p = cachedIntern(vm, key)
				if p then
					byPtr[p] = key
				elseif not byText[key] then
					byText[key] = true
					textLeft += 1
				end
			end
		end
	end
	if nb and anyStr then
		local s15 = band(Layout.tags.string, 15)
		for i = 0, n - 1 do
			local base = i * 32
			if band(b_u32(nb, base + 28), 15) == s15 then
				local kp = q(nb, base + 16)
				local key = byPtr[kp]
				if not key and textLeft > 0 then
					local txt = tsCached(kp)
					if txt and byText[txt] then
						key = txt
						byText[txt] = nil
						textLeft -= 1
						rememberIntern(vm, txt, kp)
					end
				end
				if key and not slots[key] then slots[key] = { addr = h.node + base, nb = nb, at = base, kb = keyBytes(nb, base) } end
			end
		end
	end
	for _, key in keys do
		if slots[key] == nil and not (nb and type(key) == "string") then
			local slot = findSlot(t, key, vm)
			if slot then
				local arr = h.sizearray > 0 and slot >= h.array and slot < h.array + h.sizearray * 16
				local kb
				if not arr then
					local kbuf = rd(slot, 32)
					kb = kbuf and keyBytes(kbuf, 0) or false
				end
				slots[key] = { addr = slot, arr = arr, kb = kb }
			end
		end
	end
	return slots, h
end

local function tagOfValue(v)
	local T = Layout.tags
	local tv = type(v)
	if v == nil then return 0 end
	if tv == "boolean" then return T.boolean end
	if tv == "number" then return T.number end
	if tv == "string" then return T.string end
	if tv == "vector" or (tv == "userdata" and typeof and typeof(v) == "Vector3") then return T.vector end
	if isInstanceValue(v) then return T.userdata end
	local inf = infoOf(v)
	if inf then return inf.tag end
	return nil
end

local function valueWidth(tt)
	local T = Layout.tags
	if tt == T.boolean then return 4 end
	if tt == T.vector then return 12 end
	return 8
end

function SevereGC.getmany(t, keys)
	requireAttached()
	local a, inf = addrOf(t, "table")
	local vm = (inf and inf.vm) or Current
	local slots = slotsOf(a, keys, vm)
	if not slots then return nil end
	local out = {}
	for key, sl in slots do
		local vb, at = sl.nb, sl.at
		if not vb then vb, at = rd(sl.addr, 16), 0 end
		if vb then out[key] = decodeTV(vb, at, vm) end
	end
	return out
end

function SevereGC.setmany(t, values, opts)
	requireAttached()
	if not memWrite then error("SevereGC: memory.writebuffer is not available", 2) end
	opts = opts or {}
	local a, inf = addrOf(t, "table")
	local vm = (inf and inf.vm) or Current
	local keys = {}
	for k in values do keys[#keys + 1] = k end
	local slots, h = slotsOf(a, keys, vm)
	if not slots then return nil, "the table no longer exists" end
	local plan = {}
	local unchanged, skipped, missing = 0, 0, 0
	for k, v in values do
		local sl = slots[k]
		local cur, at
		if sl then
			cur, at = sl.nb, sl.at
			if not cur then cur, at = rd(sl.addr, 16), 0 end
		end
		if not cur then
			missing += 1
		else
			local oldtt = b_i32(cur, at + 12)
			if opts.SameType and tagOfValue(v) ~= oldtt then
				skipped += 1
			else
				local b = encodeTV(v, vm)
				local newtt = b_i32(b, 12)
				if opts.SameType and oldtt ~= newtt then
					skipped += 1
				elseif oldtt == newtt and b_str(cur, at, valueWidth(newtt)) == b_str(b, 0, valueWidth(newtt)) then
					unchanged += 1
				else
					plan[#plan + 1] = { slot = sl.addr, oldtt = oldtt, b = b, kb = sl.kb, arr = sl.arr, fromNb = sl.nb ~= nil }
				end
			end
		end
	end
	if #plan > 0 then
		local fresh
		for _, w in plan do
			if w.fromNb then
				fresh = rd(h.node, (2 ^ h.lsz) * 32)
				break
			end
		end
		for _, w in plan do
			local cb, at
			if w.fromNb then
				cb, at = fresh, w.slot - h.node
			else
				cb, at = rd(w.slot, w.arr and 16 or 32), 0
			end
			local same = cb ~= nil and b_i32(cb, at + 12) == w.oldtt
			if same and not w.arr then same = w.kb ~= nil and w.kb ~= false and keyBytes(cb, at) == w.kb end
			w.same = same
		end
		local h2 = readTableHeader(a)
		if not h2 or h2.node ~= h.node or h2.lsz ~= h.lsz or h2.array ~= h.array or h2.sizearray ~= h.sizearray then
			return nil, "the table changed while writing; try again"
		end
		local written = 0
		for _, w in plan do
			if w.same then
				writeSlotKnown(w.slot, w.oldtt, w.b)
				written += 1
			else
				skipped += 1
			end
		end
		return written, unchanged, skipped, missing
	end
	return 0, unchanged, skipped, missing
end

function SevereGC.keys(t)
	requireAttached()
	local a, inf = addrOf(t, "table")
	local out = {}
	for _, e in tableEntries(a, (inf and inf.vm) or Current) do out[#out + 1] = e[1] end
	return out
end

function SevereGC.pairs(t)
	requireAttached()
	local a, inf = addrOf(t, "table")
	local list = tableEntries(a, (inf and inf.vm) or Current)
	local i = 0
	return function()
		i += 1
		local e = list[i]
		if e then return e[1], e[2] end
		return nil
	end
end

function SevereGC.snapshot(t, depth, seen)
	requireAttached()
	depth = depth or 1
	seen = seen or {}
	local a, inf = addrOf(t, "table")
	if seen[a] then return seen[a] end
	local out = {}
	seen[a] = out
	for _, e in tableEntries(a, (inf and inf.vm) or Current) do
		local v = e[2]
		if depth > 1 and infoOf(v) and infoOf(v).kind == "table" then v = SevereGC.snapshot(v, depth - 1, seen) end
		out[e[1]] = v
	end
	return out
end

function SevereGC.address(x)
	local inf = infoOf(x)
	return inf and inf.addr or nil
end

function SevereGC.isremote(x)
	return infoOf(x) ~= nil
end

function SevereGC.isalive(x)
	if not Layout then return false end
	local inf = infoOf(x)
	if not inf then return isInstanceValue(x) end
	if inf.kind == "lightuserdata" then return true end
	local hb = rd(inf.addr, 8)
	return hb ~= nil and b_u8(hb, 1) == inf.tag
end

function SevereGC.typeof(x)
	local inf = infoOf(x)
	if inf then return inf.kind end
	return typeof(x)
end

function SevereGC.wrap(addr, kind)
	requireAttached()
	if type(addr) ~= "number" then error("SevereGC: wrap expects an address", 2) end
	local T = Layout.tags
	local tt
	if kind == "table" then tt = T.table
	elseif kind == "function" then tt = T.func
	elseif kind == "userdata" then tt = T.userdata
	elseif kind == "thread" then tt = T.thread
	elseif kind == "proto" then
		ensureLazy("functions")
		tt = T.proto
	end
	if not tt then tt = tagAt(addr) end
	return wrap(addr, tt, Current)
end

local function tableHeaderFromBuf(addr, buf, at)
	local Tb = Layout.table
	if at + Tb.span > b_len(buf) then return nil end
	local lsz = b_u8(buf, at + Tb.lsz)
	local node = q(buf, at + Tb.node)
	local meta = Tb.meta and q(buf, at + Tb.meta) or 0
	local sa = Tb.sizearray and b_i32(buf, at + Tb.sizearray) or 0
	local arr = Tb.array and decodePtr(addr + Tb.array, buf, at + Tb.array, Tb.arrayEnc) or 0
	return lsz, node, meta, sa, arr
end

local function lowerBound(items, v)
	local lo, hi = 1, #items + 1
	while lo < hi do
		local mid = (lo + hi) // 2
		if items[mid].node < v then lo = mid + 1 else hi = mid end
	end
	return lo
end

local function sweepNodeArrays(vm, items, ctx, process)
	if #items == 0 then return false end
	local pages = listPages(vm, "ng", ctx)
	table.sort(pages, function(x, y) return x[1] < y[1] end)
	local np = #pages
	local buckets = {}
	local leftovers = {}
	for _, it in items do
		local node = it.node
		local lo, hi = 1, np
		local found = 0
		while lo <= hi do
			local mid = (lo + hi) // 2
			local e = pages[mid]
			if node < e[1] then
				hi = mid - 1
			elseif node >= e[1] + e[2] then
				lo = mid + 1
			else
				found = mid
				break
			end
		end
		if found > 0 and node + it.size <= pages[found][1] + pages[found][2] then
			local b = buckets[found]
			if not b then b = {} buckets[found] = b end
			b[#b + 1] = it
		else
			leftovers[#leftovers + 1] = it
		end
	end
	for idx, list in buckets do
		local e = pages[idx]
		local buf = e[2] <= 0x10000 and rd(e[1], e[2]) or nil
		if buf then
			local blen = b_len(buf)
			for _, it in list do
				local off = it.node - e[1]
				if off + it.size <= blen then
					if process(it, buf, off) == true then return true end
				end
			end
		else
			for _, it in list do leftovers[#leftovers + 1] = it end
		end
		if ctx and not step(ctx) then return false end
	end
	for _, it in leftovers do
		local buf = rd(it.node, it.size)
		if buf and process(it, buf, 0) == true then return true end
		if ctx and not step(ctx) then return false end
	end
	return false
end

local function compileQuery(query)
	if type(query) == "function" then return { fn = query, keys = {}, eq = {} } end
	if type(query) == "string" then query = { query } end
	local keys, eq, fn = {}, {}, nil
	local seen = {}
	for k, v in query do
		if type(k) == "number" then
			if not seen[v] then
				seen[v] = true
				keys[#keys + 1] = v
			end
		elseif k == "Where" and type(v) == "function" then
			fn = v
		else
			eq[k] = v
		end
	end
	return { keys = keys, eq = eq, fn = fn }
end

local function valueMatchesTV(nb, o, want, vm, strPtrs, instPtrs)
	local T = Layout.tags
	local tt = b_i32(nb, o + 12)
	local tw = type(want)
	if want == nil then return tt == 0 end
	if tw == "number" then return tt == T.number and b_f64(nb, o) == want end
	if tw == "boolean" then return tt == T.boolean and ((b_u32(nb, o) ~= 0) == want) end
	if tw == "string" then
		if tt ~= T.string then return false end
		if strPtrs then
			local p = strPtrs[want]
			if p then return q(nb, o) == p end
			if p == false then return false end
		end
		return tsRead(q(nb, o), #want) == want
	end
	if isInstanceValue(want) then
		if tt ~= T.userdata or not Layout.udata then return false end
		local ia = instPtrs and instPtrs[want]
		if ia == nil then
			ia = instAddr(want) or false
			if instPtrs then instPtrs[want] = ia end
		end
		if not ia then return false end
		return udataInstanceAddr(q(nb, o)) == ia
	end
	local inf = infoOf(want)
	if inf then return tt == inf.tag and q(nb, o) == inf.addr end
	return false
end

local PageIdx = setmetatable({}, { __mode = "k" })

local function pageIndex(vm, kind, maxAge)
	local cache = PageIdx[vm]
	if not cache then
		cache = {}
		PageIdx[vm] = cache
	end
	local idx = cache[kind]
	local now = clock()
	if idx and now - idx.t < (maxAge or SevereGC.PageIndexMaxAge or 3) then return idx end
	local pages = listPages(vm, kind, nil)
	idx = { t = now, list = pages, byBs = {}, bsList = {} }
	for _, e in pages do
		local l = idx.byBs[e[3]]
		if not l then
			l = {}
			idx.byBs[e[3]] = l
			idx.bsList[#idx.bsList + 1] = e[3]
		end
		l[#l + 1] = e
	end
	table.sort(idx.bsList)
	cache[kind] = idx
	return idx
end

local function classFor(idx, need)
	for _, bs in idx.bsList do
		if bs >= need then return bs end
	end
	return nil
end

local function packU32(n)
	return string.char(n % 256, (n // 256) % 256, (n // 65536) % 256, (n // 16777216) % 256)
end

local function packPtr(p)
	local lo = p % TWO32
	local hi = (p - lo) / TWO32
	return packU32(lo) .. packU32(hi)
end

local function resolveNeedlesFast(vm, strPtrs, ctx)
	local St = Layout.str
	local S = Layout.tags.string
	local P = Layout.pages
	local idx = pageIndex(vm, "gc")
	local groups = {}
	local pending = 0
	for s, v in strPtrs do
		if v == false then
			local need = St.data + #s + 1
			local cls = classFor(idx, need)
			for _, bs in { cls, need } do
				if bs and idx.byBs[bs] then
					local g = groups[bs]
					if not g then
						g = {}
						groups[bs] = g
					end
					g[#g + 1] = s
				end
			end
			pending += 1
		end
	end
	if pending == 0 then return end
	for bs, list in groups do
		for _, e in idx.byBs[bs] do
			local left = false
			for _, s in list do
				if strPtrs[s] == false then left = true break end
			end
			if not left then break end
			local pg, pgs = e[1], e[2]
			local buf = pgs <= 0x10000 and rd(pg, pgs) or rd(pg, math.min(pgs, P.data + St.data + 0x1000))
			local at, stop
			if buf then at, stop = pageRange(buf, P, pgs, bs) end
			if at then
				local str = buffer.tostring(buf)
				local adj = St.data - St.len == 4
				local back = adj and St.len or St.data
				for _, s in list do
					if strPtrs[s] == false then
						local pat = adj and (packU32(#s) .. s .. "\0") or (s .. "\0")
						local init = 1
						while true do
							local p = string.find(str, pat, init, true)
							if not p then break end
							local start = p - 1 - back
							if start >= at and start < stop and (start - P.data) % bs == 0 and b_u8(buf, start + 1) == S and (adj or b_u32(buf, start + St.len) == #s) then
								strPtrs[s] = pg + start
								rememberIntern(vm, s, pg + start)
								break
							end
							init = p + 1
						end
					end
				end
			end
			if ctx then step(ctx) end
		end
	end
end

local function fastApplicable(spec)
	if not Layout.table.bs then return false end
	if spec.values and #spec.values > 0 then return false end
	if #spec.keys == 0 and next(spec.eq) == nil then return false end
	for _, k in spec.keys do
		if type(k) ~= "string" then return false end
	end
	for k in spec.eq do
		if type(k) ~= "string" then return false end
	end
	if #spec.keys + (function() local c = 0 for _ in spec.eq do c += 1 end return c end)() > 28 then return false end
	return true
end

local function fastScanTables(vm, spec, opts)
	opts = opts or {}
	SevereGC.LastScan = nil
	local ctx = newCtx(opts)
	local T, Tb, P = Layout.tags, Layout.table, Layout.pages
	if spec.metatable ~= nil and not infoOf(spec.metatable) then error("SevereGC: Metatable must be a remote table", 3) end
	local strPtrs = {}
	local function want(s)
		if strPtrs[s] == nil then strPtrs[s] = cachedIntern(vm, s) or false end
	end
	for _, k in spec.keys do want(k) end
	for k, v in spec.eq do
		want(k)
		if type(v) == "string" then want(v) end
	end
	local tA = clock()
	resolveNeedlesFast(vm, strPtrs, ctx)
	local tB = clock()
	local function early(why)
		SevereGC.LastScan = { aborted = why, msNeedles = (tB - tA) * 1000, candidates = 0 }
		return {}, why
	end
	local reqs = {}
	for _, k in spec.keys do
		if not strPtrs[k] then return early("key '" .. k .. "' does not exist in this VM") end
		reqs[#reqs + 1] = { ptr = strPtrs[k] }
	end
	for k, v in spec.eq do
		if not strPtrs[k] then return early("key '" .. k .. "' does not exist in this VM") end
		if type(v) == "string" and not strPtrs[v] then return early("value '" .. v .. "' does not exist in this VM") end
		reqs[#reqs + 1] = { ptr = strPtrs[k], eq = true, want = v }
	end
	local nreq = #reqs
	local minKeys = math.max(nreq, opts.MinKeys or 0)
	local minLsz = 0
	while 2 ^ minLsz < minKeys do minLsz += 1 end
	if opts.MinLsz and opts.MinLsz > minLsz then minLsz = opts.MinLsz end
	local metaWant = spec.metatable and infoOf(spec.metatable).addr
	local idx = pageIndex(vm, "gc")
	local tC = clock()
	local maxLsz = 17
	if opts.MaxKeys then
		maxLsz = 0
		while 2 ^ maxLsz < opts.MaxKeys do maxLsz += 1 end
		if maxLsz < minLsz then maxLsz = minLsz end
	end
	local cNode, cAddr, cLsz, byNode = {}, {}, {}, {}
	local n = 0
	local dummy = Tb.dummy
	local lszOff, nodeOff, metaOff = Tb.lsz, Tb.node, Tb.meta
	local TT = T.table
	for _, e in idx.byBs[Tb.bs] or {} do
		local pg, pgs, bs = e[1], e[2], e[3]
		local buf = rd(pg, pgs)
		local at, stop
		if buf then at, stop = pageRange(buf, P, pgs, bs) end
		if at then
			while at + bs <= stop do
				local lsz = b_u8(buf, at + lszOff)
				if lsz >= minLsz and lsz <= maxLsz and b_u8(buf, at + 1) == TT then
					local node = q(buf, at + nodeOff)
					if node ~= dummy and isptr(node) and (not metaWant or (metaOff and q(buf, at + metaOff) == metaWant)) then
						n += 1
						cNode[n], cAddr[n], cLsz[n] = node, pg + at, lsz
						byNode[node] = n
					end
				end
				at += bs
			end
		end
		if not step(ctx) then break end
	end
	local tD = clock()
	local patterns = {}
	for i, r in reqs do patterns[i] = packPtr(r.ptr) end
	local strTag15 = band(T.string, 15)
	local bits = {}
	local full = 2 ^ nreq - 1
	local ready = {}
	local function scanBuffer(pbuf, pstr, base0, bsz)
		local blen = b_len(pbuf)
		for i, r in reqs do
			local pat2 = patterns[i]
			local bit = 2 ^ (i - 1)
			local init = 1
			while true do
				local p = string.find(pstr, pat2, init, true)
				if not p then break end
				init = p + 1
				local off = p - 1
				local nodeBase, rel
				if bsz > 0 then
					if off >= P.data then
						local blk = P.data + ((off - P.data) // bsz) * bsz
						nodeBase = base0 + blk + 8
						rel = off - (blk + 8)
					end
				else
					nodeBase = base0
					rel = off
				end
				local ci = nodeBase and byNode[nodeBase]
				if ci and rel >= 0 and rel % 32 == 16 and rel < (2 ^ cLsz[ci]) * 32 and off + 16 <= blen and off >= 16 then
					if band(b_u32(pbuf, off + 12), 15) == strTag15 and b_i32(pbuf, off - 4) ~= 0 then
						if not r.eq or valueMatchesTV(pbuf, off - 16, r.want, vm, strPtrs) then
							local old = bits[ci] or 0
							local nb2 = bit32.bor(old, bit)
							if nb2 ~= old then
								bits[ci] = nb2
								if nb2 == full then ready[#ready + 1] = ci end
							end
						end
					end
				end
			end
		end
	end
	local hashEnc = Layout.str and Layout.str.hashEnc
	local useProbe = hashEnc ~= nil and opts.NoProbe ~= true
	if useProbe then
		for _, r in reqs do
			local hh = stringHash(r.ptr)
			if hh then r.hash = hh else useProbe = false end
		end
	end
	local probes = 0
	local function probeAll(i)
		if bits[i] == full then return end
		local node, lsz = cNode[i], cLsz[i]
		for _, r in reqs do
			probes += 1
			local slot, nb = probeNode(node, lsz, r.ptr, r.hash)
			if not slot then return end
			if b_i32(nb, 12) == 0 then return end
			if r.eq and not valueMatchesTV(nb, 0, r.want, vm, strPtrs) then return end
		end
		bits[i] = full
		ready[#ready + 1] = i
	end
	local limit = opts.Limit or math.huge
	local early = opts.Limit ~= nil and spec.fn == nil
	local halt = false
	local done = {}
	local pagesRead, singles = 0, 0
	local nSmall = 0
	if useProbe then
		for i = 1, n do
			if cLsz[i] <= 4 then nSmall += 1 end
		end
	end
	local cluster = not useProbe or nSmall >= (opts.ClusterMin or SevereGC.ClusterMin or 4096)
	if cluster then
		local buckets = {}
		for i = 1, n do
			if not useProbe or cLsz[i] <= 4 then
				local w = cNode[i] // 16384
				local bk = buckets[w]
				if not bk then
					bk = {}
					buckets[w] = bk
				end
				bk[#bk + 1] = i
			end
		end
		for _, list in buckets do
			for _, i in list do
				if not done[i] then
					local node = cNode[i]
					local handled = false
					local hb = rd(node - 8, 8)
					local pb = hb and q(hb, 0) or -1
					if isptr(pb) and pb < node and node - pb < 0x10000 then
						local hh = rd(pb, P.data + 8)
						if hh then
							local pgs, bsz = b_i32(hh, P.ps), b_i32(hh, P.bs)
							local rel = node - 8 - pb - P.data
							if P.sizes[pgs] and bsz >= 16 and bsz <= 0x2000 and rel >= 0 and rel % bsz == 0 then
								local pbuf = rd(pb, pgs)
								if pbuf then
									pagesRead += 1
									scanBuffer(pbuf, buffer.tostring(pbuf), pb, bsz)
									for ww = pb // 16384, (pb + pgs) // 16384 do
										local bl = buckets[ww]
										if bl then
											for _, j in bl do
												local nj = cNode[j]
												if nj >= pb and nj < pb + pgs then done[j] = true end
											end
										end
									end
									handled = true
								end
							end
						end
					end
					if not handled then
						done[i] = true
						if useProbe then
							probeAll(i)
						else
							singles += 1
							local nb = rd(node, (2 ^ cLsz[i]) * 32)
							if nb then scanBuffer(nb, buffer.tostring(nb), node, 0) end
						end
					end
					if not step(ctx) or (early and #ready >= limit) then
						halt = true
						break
					end
				end
			end
			if halt then break end
		end
	end
	if useProbe and not halt then
		for i = 1, n do
			if not done[i] then
				probeAll(i)
				if early and #ready >= limit then break end
				if i % 64 == 0 and not step(ctx) then break end
			end
		end
	end
	local tE = clock()
	local out = {}
	for _, i in ready do
		local h = readTableHeader(cAddr[i])
		if h and h.node == cNode[i] then
			local px = wrap(cAddr[i], T.table, vm)
			local ok = true
			if spec.fn then
				local okf, res = pcall(spec.fn, px)
				ok = okf and res == true
			end
			if ok then
				out[#out + 1] = px
				if #out >= limit then break end
			end
		end
	end
	local tF = clock()
	SevereGC.LastScan = {
		candidates = n, pagesRead = pagesRead, singles = singles, tablePages = #(idx.byBs[Tb.bs] or {}), minLsz = minLsz, maxLsz = maxLsz,
		probe = useProbe, probes = probes, clustered = cluster, yields = ctx.yields or 0, msYield = (ctx.yieldTime or 0) * 1000,
		msNeedles = (tB - tA) * 1000, msIndex = (tC - tB) * 1000, msTables = (tD - tC) * 1000, msNodes = (tE - tD) * 1000, msResults = (tF - tE) * 1000,
	}
	return out, ctx.truncated and "truncated" or nil
end

local function scanTables(vm, spec, opts)
	opts = opts or {}
	SevereGC.LastScan = nil
	local ctx = newCtx(opts)
	local T = Layout.tags
	if spec.metatable ~= nil and not infoOf(spec.metatable) then error("SevereGC: Metatable must be a remote table", 3) end
	local needles = {}
	for _, k in spec.keys do if type(k) == "string" then needles[#needles + 1] = k end end
	for k, v in spec.eq do
		if type(k) == "string" then needles[#needles + 1] = k end
		if type(v) == "string" then needles[#needles + 1] = v end
	end
	if spec.values then for _, v in spec.values do if type(v) == "string" then needles[#needles + 1] = v end end end
	local strPtrs, pending, byLen = {}, 0, {}
	for _, s in needles do
		if strPtrs[s] == nil then
			local c = cachedIntern(vm, s)
			if c then
				strPtrs[s] = c
			else
				strPtrs[s] = false
				pending += 1
				local l = byLen[#s]
				if not l then l = {} byLen[#s] = l end
				l[#l + 1] = s
			end
		end
	end
	local instPtrs = {}
	local nreq = #spec.keys
	for _ in spec.eq do nreq += 1 end
	local values = spec.values and #spec.values > 0 and spec.values or nil
	local needArray = values ~= nil
	for _, k in spec.keys do if type(k) == "number" then needArray = true end end
	for k in spec.eq do if type(k) == "number" then needArray = true end end
	local minLsz = 0
	if not needArray then
		while 2 ^ minLsz < nreq do minLsz += 1 end
	end
	local nodeItems, arrItems, plain = {}, {}, {}
	local metaWant = spec.metatable and infoOf(spec.metatable).addr
	local noConstraint = nreq == 0 and not values
	local St = Layout.str
	local dummy = Layout.table.dummy
	local filter = { [T.table] = true }
	if pending > 0 then filter[T.string] = true end
	forEachObject(vm, filter, function(addr, tt, buf, at, bsz)
		if tt == T.table then
			local lsz, node, meta, sa, arr = tableHeaderFromBuf(addr, buf, at)
			if lsz and lsz <= 17 and (not metaWant or meta == metaWant) then
				if noConstraint then
					plain[#plain + 1] = addr
				else
					local hasNode = isptr(node) and node ~= dummy
					if hasNode and lsz >= minLsz then
						nodeItems[#nodeItems + 1] = { addr = addr, node = node, size = 2 ^ lsz * 32, n = 2 ^ lsz }
					end
					if needArray and sa > 0 and isptr(arr) then
						local n = math.min(sa, 0x10000)
						arrItems[#arrItems + 1] = { addr = addr, node = arr, size = n * 16, n = n, isArray = true }
					end
				end
			end
		else
			local len = b_u32(buf, at + St.len)
			local l = byLen[len]
			if l then
				local text
				if at + St.data + len <= b_len(buf) then text = b_str(buf, at + St.data, len) else text = tsRead(addr) end
				for _, s in l do
					if strPtrs[s] == false and text == s then
						strPtrs[s] = addr
						rememberIntern(vm, s, addr)
					end
				end
			end
		end
		return false
	end, ctx)
	for _, k in spec.keys do
		if type(k) == "string" and not strPtrs[k] then return {}, "key '" .. k .. "' does not exist in this VM" end
	end
	for k, v in spec.eq do
		if type(k) == "string" and not strPtrs[k] then return {}, "key '" .. k .. "' does not exist in this VM" end
		if type(v) == "string" and not strPtrs[v] then return {}, "value '" .. v .. "' does not exist in this VM" end
	end
	if values then
		for _, v in values do
			if type(v) == "string" and not strPtrs[v] then return {}, "value '" .. v .. "' does not exist in this VM" end
		end
	end
	local found = {}
	local limit = opts.Limit or math.huge
	local function accept(addr)
		local px = wrap(addr, T.table, vm)
		if spec.fn then
			local okf, res = pcall(spec.fn, px)
			if not (okf and res == true) then return false end
		end
		found[#found + 1] = px
		return #found >= limit
	end
	if noConstraint then
		for i, addr in plain do
			if accept(addr) then break end
			if i % 64 == 0 and not step(ctx) then break end
		end
		return found, ctx.truncated and "truncated" or nil
	end
	local state = {}
	local scratch = { k = {}, e = {}, v = {}, have = 0, vhave = 0 }
	local function stateOf(addr)
		if not needArray then
			wipe(scratch.k)
			wipe(scratch.e)
			wipe(scratch.v)
			scratch.have = 0
			scratch.vhave = 0
			return scratch
		end
		local s = state[addr]
		if not s then
			s = { k = {}, e = {}, v = {}, have = 0, vhave = 0 }
			state[addr] = s
		end
		return s
	end
	local function markKey(s, k)
		if not s.k[k] then s.k[k] = true s.have += 1 end
	end
	local function markEq(s, k)
		if not s.e[k] then s.e[k] = true s.have += 1 end
	end
	local function markValues(s, buf, o)
		if not values then return end
		for vi, v in values do
			if not s.v[vi] and valueMatchesTV(buf, o, v, vm, strPtrs, instPtrs) then
				s.v[vi] = true
				s.vhave += 1
			end
		end
	end
	local nvalues = values and #values or 0
	local function complete(s)
		return s.have >= nreq and s.vhave >= nvalues
	end
	local function verifyAndAccept(addr, node, isArray)
		local h = readTableHeader(addr)
		if not h then return false end
		if isArray then
			if h.array ~= node then return false end
		elseif h.node ~= node then
			return false
		end
		return accept(addr)
	end
	local strTag = band(T.string, 15)
	local numTag = band(T.number, 15)
	local boolTag = band(T.boolean, 15)
	local stopped = sweepNodeArrays(vm, nodeItems, ctx, function(it, buf, off)
		local s = stateOf(it.addr)
		for i = 0, it.n - 1 do
			local base = off + i * 32
			if b_i32(buf, base + 12) ~= 0 then
				local ktt = band(b_u32(buf, base + 28), 15)
				if ktt == strTag then
					local kp = q(buf, base + 16)
					for _, k in spec.keys do
						if type(k) == "string" and strPtrs[k] == kp then markKey(s, k) end
					end
					for k, v in spec.eq do
						if type(k) == "string" and strPtrs[k] == kp and valueMatchesTV(buf, base, v, vm, strPtrs, instPtrs) then markEq(s, k) end
					end
				elseif ktt == numTag then
					local kv = b_f64(buf, base + 16)
					for _, k in spec.keys do
						if k == kv then markKey(s, k) end
					end
					for k, v in spec.eq do
						if k == kv and valueMatchesTV(buf, base, v, vm, strPtrs, instPtrs) then markEq(s, k) end
					end
				elseif ktt == boolTag then
					local kv = b_u32(buf, base + 16) ~= 0
					for _, k in spec.keys do
						if k == kv then markKey(s, k) end
					end
				end
				markValues(s, buf, base)
			end
		end
		if not needArray and complete(s) then
			if verifyAndAccept(it.addr, it.node, false) then return true end
		end
		return false
	end)
	if needArray and not stopped and #found < limit then
		sweepNodeArrays(vm, arrItems, ctx, function(it, buf, off)
			local s = stateOf(it.addr)
			for _, k in spec.keys do
				if type(k) == "number" and k >= 1 and k <= it.n and k % 1 == 0 and b_i32(buf, off + (k - 1) * 16 + 12) ~= 0 then markKey(s, k) end
			end
			for k, v in spec.eq do
				if type(k) == "number" and k >= 1 and k <= it.n and k % 1 == 0 and valueMatchesTV(buf, off + (k - 1) * 16, v, vm, strPtrs, instPtrs) then markEq(s, k) end
			end
			if values then
				for i = 0, it.n - 1 do
					if b_i32(buf, off + i * 16 + 12) ~= 0 then markValues(s, buf, off + i * 16) end
					if s.vhave >= nvalues then break end
				end
			end
			s.arrDone = true
			return false
		end)
		local i = 0
		for addr, s in state do
			i += 1
			if complete(s) then
				if accept(addr) then break end
			end
			if i % 128 == 0 and not step(ctx) then break end
		end
	end
	return found, ctx.truncated and "truncated" or nil
end

resolveVM = function(v)
	if v == nil then return nil end
	if type(v) == "number" then return VMs[v] end
	if type(v) == "string" then
		local best
		for _, vm in VMs do
			if vm.kind == v and (not best or (vm.strings or 0) > (best.strings or 0)) then best = vm end
		end
		return best
	end
	if type(v) == "table" then
		for _, vm in VMs do
			if vm == v or vm.G == v.G then return vm end
		end
	end
	return nil
end

pickVM = function(opts)
	if opts and opts.VM ~= nil then
		local vm = resolveVM(opts.VM)
		if not vm and VMsPartial then
			SevereGC.attach(nil, { Full = true })
			vm = resolveVM(opts.VM)
		end
		if not vm then error("SevereGC: no such VM: " .. tostring(opts.VM), 3) end
		return vm
	end
	return Current
end

function SevereGC.find(query, opts)
	requireAttached()
	opts = opts or {}
	local spec = compileQuery(query)
	local vm = pickVM(opts)
	if opts.Fast ~= false and fastApplicable(spec) then return fastScanTables(vm, spec, opts) end
	local list, why = scanTables(vm, spec, opts)
	return list, why
end

function SevereGC.set(a, b, c)
	local t0 = clock()
	local values, opts
	if type(a) == "table" and not infoOf(a) then
		values, opts = a, b
	else
		values, opts = { [a] = b }, c
	end
	opts = opts or {}
	requireAttached()
	local keys = {}
	for k in values do keys[#keys + 1] = k end
	local list = SevereGC.find(keys, opts)
	local so = { SameType = opts.SameType ~= false }
	local tracked, seen = {}, {}
	local alive = true
	local function track(t)
		local addr = SevereGC.address(t)
		if not addr or seen[addr] then return end
		seen[addr] = true
		local okR, vals = pcall(SevereGC.getmany, t, keys)
		tracked[#tracked + 1] = { t = t, prev = okR and vals or nil }
	end
	local function apply()
		local w = 0
		for _, e in tracked do
			if not alive then break end
			local okW, n = pcall(SevereGC.setmany, e.t, values, so)
			if okW and n then w += n end
		end
		return w
	end
	for _, t in list do track(t) end
	local written = apply()
	if opts.Keep and task and task.spawn then
		local every = type(opts.Keep) == "number" and opts.Keep or 2
		task.spawn(function()
			local cycle = 0
			while alive do
				waitFn(every)
				if not alive then break end
				cycle += 1
				if cycle % 5 == 0 then
					local okF, more = pcall(SevereGC.find, keys, opts)
					if not alive then break end
					if okF and type(more) == "table" then
						for _, t in more do track(t) end
					end
				end
				pcall(apply)
			end
		end)
	end
	local function undo()
		alive = false
		local restored = 0
		for _, e in tracked do
			if e.prev then
				local okW, n = pcall(SevereGC.setmany, e.t, e.prev, so)
				if okW and n then restored += n end
			end
		end
		return restored
	end
	return written, #list, (clock() - t0) * 1000, undo
end

function SevereGC.first(query, opts)
	opts = opts or {}
	local o = {}
	for k, v in opts do o[k] = v end
	o.Limit = 1
	local list, why = SevereGC.find(query, o)
	return list[1], why
end

local function walkFunctions(vm, opts, visit)
	ensureLazy("functions")
	local ctx = newCtx(opts)
	local T = Layout.tags
	local need = math.max(Layout.closure.env, Layout.closure.proto) + 8
	forEachObject(vm, { [T.func] = true }, function(addr, tt, buf, at, bsz)
		if at + need > b_len(buf) then return false end
		return visit(addr, buf, at, bsz) == true
	end, ctx)
	return ctx
end

function SevereGC.getgc(includeTables, opts)
	ensureLazy("functions")
	requireAttached()
	opts = opts or {}
	local vm = pickVM(opts)
	local T = Layout.tags
	local U = Layout.udata
	local filter = { [T.func] = true }
	if includeTables then filter[T.table] = true end
	if opts.Userdata then filter[T.userdata] = true end
	if opts.Threads then filter[T.thread] = true end
	local out = {}
	local limit = opts.Limit or math.huge
	local each = opts.Each
	local raw = opts.Raw
	local count = 0
	local ctx = newCtx(opts)
	forEachObject(vm, filter, function(addr, tt, buf, at)
		count += 1
		if raw then
			out[#out + 1] = addr
			return #out >= limit
		end
		local v
		if tt == T.userdata and U and toUserdata and SevereGC.InstanceConversion ~= false then
			local ia = udataInstanceAddr(addr, buf, at)
			if ia then
				local ok, inst = pcall(toUserdata, ia)
				if ok and inst then
					v = inst
					pcall(function() InstanceUdata[inst] = { udata = addr, inst = ia, vm = vm } end)
				end
			end
		end
		if v == nil then v = wrap(addr, tt, vm) end
		if v ~= nil then
			if each then
				local okE, stop = pcall(each, v)
				if okE and stop == true then return true end
			else
				out[#out + 1] = v
			end
		end
		return count >= limit
	end, ctx)
	return out, ctx.truncated and "truncated" or nil
end

function SevereGC.getclosures(protoProxy, opts)
	ensureLazy("functions")
	requireAttached()
	local p = addrOf(protoProxy, "proto")
	local C = Layout.closure
	local vm = vmOf(protoProxy)
	local out = {}
	walkFunctions(vm, opts, function(addr, buf, at)
		if b_u8(buf, at + C.isC) == 0 and at + C.proto + 8 <= b_len(buf) then
			if decodePtr(addr + C.proto, buf, at + C.proto, C.protoEnc) == p then out[#out + 1] = wrap(addr, Layout.tags.func, vm) end
		end
		return false
	end)
	return out
end

local function kArrayHas(kb, off, n, consts, strPtrs)
	for _, want in consts do
		local hit = false
		for i = 0, n - 1 do
			if valueMatchesTV(kb, off + i * 16, want, nil, strPtrs) then hit = true break end
		end
		if not hit then return false end
	end
	return true
end

function SevereGC.filtergc(kind, filt, returnOne, opts)
	if kind ~= "table" then ensureLazy("functions") end
	requireAttached()
	filt = filt or {}
	opts = opts or {}
	local vm = pickVM(opts)
	if kind == "table" then
		local spec = { keys = {}, eq = {}, values = filt.Values, metatable = filt.Metatable }
		if filt.Keys then for _, k in filt.Keys do spec.keys[#spec.keys + 1] = k end end
		if filt.KeyValuePairs then for k, v in filt.KeyValuePairs do spec.eq[k] = v end end
		local o = {}
		for k, v in opts do o[k] = v end
		if returnOne then o.Limit = 1 end
		local list
		if o.Fast ~= false and fastApplicable(spec) then list = fastScanTables(vm, spec, o) else list = scanTables(vm, spec, o) end
		if returnOne then return list[1] end
		return list
	end
	if kind ~= "function" then error("SevereGC.filtergc: kind must be 'function' or 'table'", 2) end
	local T = Layout.tags
	local C = Layout.closure
	local Pr = Layout.proto
	local consts = filt.Constants and #filt.Constants > 0 and filt.Constants or nil
	local ups = filt.Upvalues and #filt.Upvalues > 0 and filt.Upvalues or nil
	if consts and (not Pr.k or not Pr.sizek) then error("SevereGC.filtergc: the constant layout was not derived", 2) end
	if filt.Name and not Pr.name and not C.cName then error("SevereGC.filtergc: function names were not derived", 2) end
	local needles = {}
	if filt.Name then needles[#needles + 1] = filt.Name end
	if consts then for _, c in consts do if type(c) == "string" then needles[#needles + 1] = c end end end
	if ups then for _, c in ups do if type(c) == "string" then needles[#needles + 1] = c end end end
	local strPtrs, byLen, pending = {}, {}, 0
	for _, s in needles do
		if strPtrs[s] == nil then
			local c = cachedIntern(vm, s)
			if c then
				strPtrs[s] = c
			else
				strPtrs[s] = false
				pending += 1
				local l = byLen[#s]
				if not l then l = {} byLen[#s] = l end
				l[#l + 1] = s
			end
		end
	end
	local St = Layout.str
	local ctx = newCtx(opts)
	local protos, closures = {}, {}
	local needProtoInfo = filt.Name or filt.Source or consts
	local filter = { [T.func] = true }
	if needProtoInfo and T.proto then filter[T.proto] = true end
	if pending > 0 then filter[T.string] = true end
	local cNeed = math.max(C.isC + 1, C.proto + 8, (C.cName or 0) + 8)
	local U = T.upval
	local function upvalScan(buf, at, isC, blen)
		local nup = b_u8(buf, at + C.nup)
		local base
		if isC then base = C.cUp else base = C.uprefs end
		if not base or at + base + nup * 16 > blen then return "read" end
		local refs = false
		local hit = {}
		local nhit = 0
		for i = 0, nup - 1 do
			local o = at + base + i * 16
			if U and b_i32(buf, o + 12) == U then
				refs = true
			else
				for wi, want in ups do
					if not hit[wi] and valueMatchesTV(buf, o, want, vm, strPtrs) then
						hit[wi] = true
						nhit += 1
					end
				end
			end
		end
		if nhit >= #ups then return "yes" end
		if refs then return "read" end
		return "no"
	end
	forEachObject(vm, filter, function(addr, tt, buf, at, bsz)
		local blen = b_len(buf)
		if tt == T.func then
			if at + cNeed > blen then return false end
			local isC = b_u8(buf, at + C.isC) == 1
			local upv
			if ups and pending == 0 then
				upv = upvalScan(buf, at, isC, blen)
				if upv == "no" then return false end
			end
			if isC then
				if not consts and not filt.Source then
					closures[#closures + 1] = { addr = addr, isC = true, cname = C.cName and q(buf, at + C.cName) or 0, upv = upv }
				end
			else
				closures[#closures + 1] = { addr = addr, proto = decodePtr(addr + C.proto, buf, at + C.proto, C.protoEnc), upv = upv }
			end
		elseif tt == T.proto then
			if at + 0xF0 > blen then return false end
			local rec = {}
			if filt.Name and Pr.name then rec.name = decodePtr(addr + Pr.name, buf, at + Pr.name, Pr.nameEnc) end
			if filt.Source then rec.src = decodePtr(addr + Pr.source, buf, at + Pr.source, Pr.sourceEnc) end
			if consts then
				rec.k = decodePtr(addr + Pr.k, buf, at + Pr.k, Pr.kEnc)
				rec.nk = b_i32(buf, at + Pr.sizek)
			end
			if filt.Name and pending == 0 and rec.name ~= strPtrs[filt.Name] then return false end
			protos[addr] = rec
		else
			local len = b_u32(buf, at + St.len)
			local l = byLen[len]
			if l then
				local text
				if at + St.data + len <= blen then text = b_str(buf, at + St.data, len) else text = tsRead(addr) end
				for _, s in l do
					if strPtrs[s] == false and text == s then
						strPtrs[s] = addr
						rememberIntern(vm, s, addr)
					end
				end
			end
		end
		return false
	end, ctx)
	if filt.Name and not strPtrs[filt.Name] then if returnOne then return nil end return {} end
	if consts then
		for _, c in consts do
			if type(c) == "string" and not strPtrs[c] then if returnOne then return nil end return {} end
		end
	end
	local verdict = {}
	if needProtoInfo then
		local srcText = {}
		local items = {}
		for addr, rec in protos do
			local ok = true
			if filt.Name then ok = rec.name == strPtrs[filt.Name] end
			if ok and filt.Source then
				local s = srcText[rec.src]
				if s == nil then
					s = tsRead(rec.src, 8192) or false
					srcText[rec.src] = s
				end
				ok = s ~= false and string.find(s, filt.Source, 1, true) ~= nil
			end
			if ok and consts then
				if rec.nk and rec.nk > 0 and isptr(rec.k) then
					local n = math.min(rec.nk, 0x10000)
					items[#items + 1] = { node = rec.k, size = n * 16, n = n, proto = addr }
				end
				ok = false
			end
			if ok then verdict[addr] = true end
		end
		if consts and #items > 0 then
			sweepNodeArrays(vm, items, ctx, function(it, buf, off)
				if kArrayHas(buf, off, it.n, consts, strPtrs) then verdict[it.proto] = true end
				return false
			end)
		end
	end
	if ups then
		for _, c in ups do
			if type(c) == "string" and not strPtrs[c] then
				if returnOne then return nil end
				return {}
			end
		end
	end
	local out = {}
	local limit = returnOne and 1 or (opts.Limit or math.huge)
	local function upsMatch(px)
		local okU, list = pcall(SevereGC.getupvalues, px)
		if not okU then return false end
		for _, want in ups do
			local hit = false
			for _, u in list do
				if u == want or (infoOf(u) and infoOf(want) and infoOf(u).addr == infoOf(want).addr) then hit = true break end
			end
			if not hit then return false end
		end
		return true
	end
	for idx, c in closures do
		local ok
		if c.isC then
			ok = not filt.Name or c.cname == strPtrs[filt.Name]
		elseif needProtoInfo then
			ok = verdict[c.proto] == true
		else
			ok = true
		end
		if ok then
			local px = wrap(c.addr, T.func, vm)
			if ups and c.upv ~= "yes" then ok = px ~= nil and upsMatch(px) end
			if ok and px then
				out[#out + 1] = px
				if #out >= limit then break end
			end
		end
		if idx % 64 == 0 and not step(ctx) then break end
	end
	if returnOne then return out[1] end
	return out
end

local function forEachThread(vm, opts, visit)
	ensureLazy("thread")
	local T = Layout.tags
	local P = Layout.pages
	local ctx = newCtx(opts)
	local Th = Layout.thread
	if Th and Th.bs then
		local idx = pageIndex(vm, "gc")
		for _, e in idx.byBs[Th.bs] or {} do
			local pg, pgs, bs = e[1], e[2], e[3]
			local buf = rd(pg, pgs)
			local at, stop
			if buf then at, stop = pageRange(buf, P, pgs, bs) end
			if at then
				while at + 2 <= stop do
					if b_u8(buf, at + 1) == T.thread then
						if visit(pg + at, buf, at) == true then return end
					end
					at += bs
				end
			end
			if not step(ctx) then return end
		end
		return
	end
	forEachObject(vm, { [T.thread] = true }, function(addr, tt, buf, at, bsz)
		return visit(addr, buf, at) == true
	end, ctx)
end

local function threadScript(addr, buf, at)
	local Th = Layout.thread
	if not Th or not Th.extra or not Th.extraScript then return nil end
	if at + Th.extra + 8 > b_len(buf) then return nil end
	local ex = q(buf, at + Th.extra)
	if not isptr(ex) then return nil end
	local sp = readPtrAt(ex + Th.extraScript, 0)
	if isptr(sp) then return sp end
	return nil
end

function SevereGC.getscripts(opts)
	requireAttached()
	local vm = pickVM(opts)
	local seen, out = {}, {}
	forEachThread(vm, opts, function(addr, buf, at)
		local sp = threadScript(addr, buf, at)
		if sp and not seen[sp] then
			seen[sp] = true
			if toUserdata then
				local ok, inst = pcall(toUserdata, sp)
				if ok and inst then out[#out + 1] = inst end
			else
				out[#out + 1] = sp
			end
		end
		return false
	end)
	return out
end

function SevereGC.getscriptthreads(script, opts)
	requireAttached()
	local target = type(script) == "number" and script or instAddr(script)
	if not target then error("SevereGC: could not read the script's address", 2) end
	local out = {}
	local vm = pickVM(opts)
	forEachThread(vm, opts, function(addr, buf, at)
		if threadScript(addr, buf, at) == target then out[#out + 1] = wrap(addr, Layout.tags.thread, vm) end
		return false
	end)
	return out
end

function SevereGC.getsenv(script, opts)
	requireAttached()
	local target = type(script) == "number" and script or instAddr(script)
	if not target then error("SevereGC: could not read the script's address", 2) end
	local vm = pickVM(opts)
	local Th = Layout.thread
	local env
	if Th and Th.gt and Th.extra then
		forEachThread(vm, opts, function(addr, buf, at)
			if threadScript(addr, buf, at) == target and at + Th.gt + 8 <= b_len(buf) then
				env = q(buf, at + Th.gt)
				return true
			end
			return false
		end)
		if env and isptr(env) then return wrap(env, Layout.tags.table, vm) end
	end
	local U = Layout.udata
	if not U or not U.instTag then return nil end
	local ctx = newCtx(opts)
	local strs = resolveStrings(vm, { "script" }, ctx)
	local sp = strs.script
	if not sp then return nil end
	local found
	local items = {}
	forEachObject(vm, { [Layout.tags.table] = true }, function(addr, tt, buf, at)
		local lsz, node = tableHeaderFromBuf(addr, buf, at)
		if lsz and lsz <= 17 and isptr(node) and node ~= Layout.table.dummy then
			items[#items + 1] = { addr = addr, node = node, size = 2 ^ lsz * 32, n = 2 ^ lsz }
		end
		return false
	end, ctx)
	sweepNodeArrays(vm, items, ctx, function(it, buf, off)
		for i = 0, it.n - 1 do
			local base = off + i * 32
			if band(b_u32(buf, base + 28), 15) == band(Layout.tags.string, 15) and q(buf, base + 16) == sp then
				if b_i32(buf, base + 12) == Layout.tags.userdata then
					if udataInstanceAddr(q(buf, base)) == target then
						local h = readTableHeader(it.addr)
						if h and h.node == it.node then
							found = it.addr
							return true
						end
					end
				end
			end
		end
		return false
	end)
	if found then return wrap(found, Layout.tags.table, vm) end
	return nil
end

function SevereGC.getscriptclosure(script, opts)
	ensureLazy("functions")
	requireAttached()
	local env = SevereGC.getsenv(script, opts)
	if not env then return nil end
	local envAddr = infoOf(env).addr
	local vm = vmOf(env)
	local C = Layout.closure
	local Pr = Layout.proto
	local cands = {}
	walkFunctions(vm, opts, function(addr, buf, at)
		if b_u8(buf, at + C.isC) == 0 and q(buf, at + C.env) == envAddr then
			cands[#cands + 1] = { addr = addr, proto = decodePtr(addr + C.proto, buf, at + C.proto, C.protoEnc) }
		end
		return false
	end)
	local hdr, isChild = {}, {}
	for _, c in cands do
		if hdr[c.proto] == nil then
			local pb = rd(c.proto, 0xF0)
			hdr[c.proto] = pb or false
			if pb and Pr.p and Pr.sizep then
				local n = math.min(b_i32(pb, Pr.sizep), 0x10000)
				if n > 0 then
					local ab = rd(decodePtr(c.proto + Pr.p, pb, Pr.p, Pr.pEnc), n * 8)
					if ab then
						for i = 0, n - 1 do isChild[q(ab, i * 8)] = true end
					end
				end
			end
		end
	end
	local best, bestLine
	for _, c in cands do
		local pb = hdr[c.proto]
		if pb and not isChild[c.proto] then
			local named = Pr.name and decodePtr(c.proto + Pr.name, pb, Pr.name, Pr.nameEnc) ~= 0
			local nups = Pr.nups and b_u8(pb, Pr.nups) or 0
			if not named and nups == 0 then
				local line = Pr.line and b_i32(pb, Pr.line) or 0
				if not best or line < bestLine then best, bestLine = c.addr, line end
			end
		end
	end
	return best and wrap(best, Layout.tags.func, vm) or nil
end

function SevereGC.getscriptfunctions(script, opts)
	ensureLazy("functions")
	requireAttached()
	local env = SevereGC.getsenv(script, opts)
	if not env then return {} end
	local envAddr = infoOf(env).addr
	local vm = pickVM(opts)
	local C = Layout.closure
	local out = {}
	walkFunctions(vm, opts, function(addr, buf, at)
		if q(buf, at + C.env) == envAddr then out[#out + 1] = wrap(addr, Layout.tags.func, vm) end
		return false
	end)
	return out
end

function SevereGC.getrenv(opts)
	ensureLazy("thread")
	requireAttached()
	local vm = pickVM(opts)
	local Th = Layout.thread
	if not Th or not Th.gt then return nil end
	return wrap(readPtrAt(vm.main + Th.gt, 0), Layout.tags.table, vm)
end

function SevereGC.getthreads(opts)
	requireAttached()
	local vm = pickVM(opts)
	local out = {}
	forEachThread(vm, opts, function(addr)
		out[#out + 1] = wrap(addr, Layout.tags.thread, vm)
		return false
	end)
	return out
end

function SevereGC.update(t, fields)
	requireAttached()
	local a, inf = addrOf(t, "table")
	local vm = (inf and inf.vm) or Current
	local written = 0
	for k, v in fields do
		local ok = pcall(tableSet, a, k, v, vm)
		if ok then written += 1 end
	end
	return written
end

local function differs(a, b)
	if type(a) == "number" and type(b) == "number" then return math.abs(a - b) > 1e-6 end
	return a ~= b
end

function SevereGC.write(query, fields, opts)
	requireAttached()
	local written = 0
	for _, t in SevereGC.find(query, opts) do
		local want = fields
		if type(fields) == "function" then
			local ok, res = pcall(fields, t)
			want = ok and res or nil
		end
		if type(want) == "table" then
			for k, v in want do
				local cur = tableGet(infoOf(t).addr, k, infoOf(t).vm)
				if differs(cur, v) and pcall(tableSet, infoOf(t).addr, k, v, infoOf(t).vm) then written += 1 end
			end
		end
	end
	return written
end

local Lock = {}
Lock.__index = Lock
local Locks = setmetatable({}, { __mode = "k" })

function Lock:refind()
	local spec = compileQuery(self.Query)
	if type(self.Fields) == "table" then
		for k in self.Fields do
			if spec.eq[k] ~= nil then
				spec.eq[k] = nil
				spec.keys[#spec.keys + 1] = k
			end
		end
	end
	local okF, list, why = pcall(scanTables, pickVM(self.Options), spec, self.Options)
	if not okF then
		self.Error = list
		return #self.Targets
	end
	if why then
		self.Error = why
		if #list == 0 then return #self.Targets end
	end
	local keep = {}
	for _, t in list do keep[infoOf(t).addr] = true end
	for _, t in self.Targets do
		local inf = infoOf(t)
		if inf and not keep[inf.addr] and readTableHeader(inf.addr) then
			keep[inf.addr] = true
			list[#list + 1] = t
		end
	end
	self.Targets = list
	self.Slots = {}
	self.Stale = false
	return #list
end

function Lock:step()
	if not Layout then return 0 end
	local alive = 0
	for i, t in self.Targets do
		local inf = infoOf(t)
		local h = inf and readTableHeader(inf.addr)
		if h then
			alive += 1
			local want = self.Fields
			if type(want) == "function" then
				local ok, res = pcall(want, t)
				want = ok and res or nil
			end
			if type(want) == "table" then
				local slots = self.Slots[inf.addr]
				if not slots or slots.node ~= h.node or slots.lsz ~= h.lsz or slots.array ~= h.array or slots.sa ~= h.sizearray then
					slots = { node = h.node, lsz = h.lsz, array = h.array, sa = h.sizearray, at = {} }
					self.Slots[inf.addr] = slots
				end
				for k, v in want do
					local slot = slots.at[k]
					if slot == nil then
						slot = findSlot(inf.addr, k, inf.vm) or false
						slots.at[k] = slot
					end
					if slot then
						local vb = rd(slot, 16)
						local cur = vb and decodeTV(vb, 0, inf.vm)
						if vb and differs(cur, v) then
							local saved = self.Originals[inf.addr]
							if not saved then
								saved = { vm = inf.vm, fields = {} }
								self.Originals[inf.addr] = saved
							end
							if saved.fields[k] == nil and cur ~= nil then saved.fields[k] = cur end
							local okW = pcall(function()
								local b = encodeTV(v, inf.vm)
								local h2 = readTableHeader(inf.addr)
								if not h2 or h2.node ~= h.node or h2.array ~= h.array then error("moved") end
								writeSlot(slot, b)
							end)
							if okW then self.Writes += 1 else slots.at[k] = nil end
						end
					end
				end
			end
		end
		if i % 64 == 0 and waitFn and coroutine.isyieldable() then waitFn() end
	end
	if alive < #self.Targets then self.Stale = true end
	return alive
end

function Lock:stop(restore)
	self.Running = false
	Locks[self] = nil
	if restore ~= false and Layout then
		for a, saved in self.Originals do
			for k, v in saved.fields do pcall(tableSet, a, k, v, saved.vm) end
		end
		self.Originals = {}
	end
end

function Lock:count()
	return #self.Targets
end

function SevereGC.lock(query, fields, opts)
	requireAttached()
	opts = opts or {}
	local h = setmetatable({
		Query = query,
		Fields = fields,
		Options = opts,
		Targets = {},
		Originals = {},
		Slots = {},
		Writes = 0,
		Running = true,
		Stale = false,
	}, Lock)
	Locks[h] = true
	h:refind()
	local interval = (opts.IntervalMs or 50) / 1000
	local refindEvery = opts.RefindMs and opts.RefindMs / 1000 or nil
	if task and task.spawn then
		task.spawn(function()
			local lastFind = clock()
			while h.Running and Layout do
				local ok, err = pcall(h.step, h)
				if not ok then
					h.Error = err
					note("lock: " .. tostring(err))
				end
				if refindEvery and clock() - lastFind >= refindEvery then
					pcall(h.refind, h)
					lastFind = clock()
				end
				if waitFn then waitFn(interval) else break end
			end
		end)
	end
	return h
end

local function chooseDefault(list)
	local best
	for _, vm in list do
		if vm.kind == "game" then
			if not best or (vm.strings or 0) > (best.strings or 0) then best = vm end
		end
	end
	if best then return best end
	for _, vm in list do
		if not best or (vm.strings or 0) > (best.strings or 0) then best = vm end
	end
	return best
end

local function anchorInstance(list)
	local U = Layout.udata
	local Th = Layout.thread
	if not U or not Th or not Th.gt then return false end
	local okG, dm = pcall(instAddr, game)
	if not okG or not dm then return false end
	for _, vm in list do
		local gt = readPtrAt(vm.main + Th.gt, 0)
		if isptr(gt) then
			local ok, slot = pcall(findSlot, gt, "game", vm)
			if ok and slot then
				local vb = rd(slot, 16)
				if vb and b_i32(vb, 12) == Layout.tags.userdata then
					local u = q(vb, 0)
					local ub = rd(u, U.data + 0x40)
					if ub then
						local tag = b_u8(ub, U.tag)
						for off = 0, 0x38, 8 do
							if q(ub, U.data + off) == dm then
								U.instGroups = { [tag] = off }
								U.instTag, U.instOff = tag, off
								U.anchored = true
								note(string.format("Instance userdata anchored on game: tag %d, data+0x%x", tag, off))
								return true
							end
						end
					end
				end
			end
		end
	end
	return false
end

local function validateNumberTag(list)
	local Th = Layout.thread
	if not Th or not Th.gt then return false end
	for _, vm in list do
		local gt = readPtrAt(vm.main + Th.gt, 0)
		if isptr(gt) then
			local ok, slot = pcall(findSlot, gt, "math", vm)
			if ok and slot then
				local vb = rd(slot, 16)
				if vb and b_i32(vb, 12) == Layout.tags.table then
					local ok2, ps = pcall(findSlot, q(vb, 0), "pi", vm)
					if ok2 and ps then
						local pb = rd(ps, 16)
						if pb and math.abs(b_f64(pb, 0) - math.pi) < 1e-12 then
							local tt = b_i32(pb, 12)
							if tt ~= Layout.tags.number then
								note("number tag corrected from " .. Layout.tags.number .. " to " .. tt)
								Layout.tags.number = tt
							end
							Layout.numberChecked = true
							return true
						end
					end
				end
			end
		end
	end
	return false
end

local function classifyFast(vm)
	local Pr, P, PT = Layout.proto, Layout.pages, Layout.tags.proto
	if not (Pr and Pr.bs and Pr.source) then return nil end
	local list = pageIndex(vm, "gc").byBs[Pr.bs] or {}
	if #list == 0 then return nil end
	local stride = math.max(1, #list // 24)
	local core, game, total = 0, 0, 0
	local seen = {}
	for pi = 1, #list, stride do
		local e = list[pi]
		local buf = rd(e[1], e[2])
		local at, stop
		if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
		if at then
			while at + e[3] <= stop do
				if b_u8(buf, at + 1) == PT then
					local d = decodePtr(e[1] + at + Pr.source, buf, at + Pr.source, Pr.sourceEnc)
					local text = seen[d]
					if text == nil then
						text = tsRead(d, 256) or false
						seen[d] = text
					end
					if text then
						total += 1
						if sourceKind(text) == "core" then core += 1 else game += 1 end
					end
				end
				at += e[3]
			end
		end
		if total >= 300 then break end
	end
	if total < 10 then return nil end
	vm.coreProtos, vm.gameProtos = core, game
	if core >= total * 0.6 then vm.kind = "core" else vm.kind = "game" end
	return vm.kind
end

local HashEncs = { "add", "xor", "ssub", "fsub", "plain" }

local function deriveStrHash(vm)
	local St, T, Tb, P = Layout.str, Layout.tags, Layout.table, Layout.pages
	if not (St and St.hash and Tb and Tb.bs and Tb.node and Tb.lsz) then return false, "layout incomplete" end
	local s15 = band(T.string, 15)
	local list = pageIndex(vm, "gc").byBs[Tb.bs] or {}
	local heads, samples = {}, {}
	local n5, used = 0, 0
	local function enough()
		return (n5 >= 300 and #heads >= 500 and #samples >= 24) or used >= 400
	end
	local stride = math.max(1, #list // 300)
	for pass = 1, stride do
		for pi = pass, #list, stride do
			local e = list[pi]
			local buf = rd(e[1], e[2])
			local at, stop
			if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
			if at then
				used += 1
				while at + e[3] <= stop do
					if b_u8(buf, at + 1) == T.table then
						local lsz = b_u8(buf, at + Tb.lsz)
						if lsz >= 2 and lsz <= 8 and (lsz >= 5 or #heads < 300) then
							local node = q(buf, at + Tb.node)
							if node ~= Tb.dummy and isptr(node) then
								local n = 2 ^ lsz
								local nb = rd(node, n * 32)
								if nb then
									local pointed = {}
									for i = 0, n - 1 do
										local nx = b_u32(nb, i * 32 + 28) // 16
										if nx >= 0x8000000 then nx -= 0x10000000 end
										if nx ~= 0 then pointed[i + nx] = true end
									end
									local keys = {}
									for i = 0, n - 1 do
										if band(b_u32(nb, i * 32 + 28), 15) == s15 then
											local kp = q(nb, i * 32 + 16)
											if isptr(kp) then
												keys[#keys + 1] = { i = i, p = kp }
												if not pointed[i] then
													heads[#heads + 1] = { p = kp, i = i, lsz = lsz }
													if lsz >= 5 then n5 += 1 end
												end
											end
										end
									end
									if lsz >= 5 and #samples < 24 and #keys >= 4 then samples[#samples + 1] = { nb = nb, lsz = lsz, keys = keys } end
								end
							end
						end
					end
					at += e[3]
				end
			end
			if enough() then break end
		end
		if enough() then break end
	end
	if n5 < 50 or #heads < 100 then return false, string.format("too few chain heads (%d, %d in big tables)", #heads, n5) end
	local storedBy = {}
	local function storedOf(p)
		local sv = storedBy[p]
		if sv == nil then
			local hb = rd(p + St.hash, 4)
			sv = hb and b_u32(hb, 0) or false
			storedBy[p] = sv
		end
		return sv
	end
	local bestEnc, best5, bestA = nil, -1, -1
	for _, enc in HashEncs do
		local hit5, tot5, hitA, totA = 0, 0, 0, 0
		for _, hd in heads do
			local sv = storedOf(hd.p)
			if sv then
				local okH = band(decodeHash(sv, (hd.p + St.hash) % TWO32, enc), 2 ^ hd.lsz - 1) == hd.i
				totA += 1
				if okH then hitA += 1 end
				if hd.lsz >= 5 then
					tot5 += 1
					if okH then hit5 += 1 end
				end
			end
		end
		local r5 = tot5 > 0 and hit5 / tot5 or 0
		local rA = totA > 0 and hitA / totA or 0
		if r5 > best5 or (r5 == best5 and rA > bestA) then bestEnc, best5, bestA = enc, r5, rA end
	end
	if not bestEnc or best5 < 0.97 or bestA < 0.97 then
		return false, string.format("no hash encoding fits (best %s %.3f / %.3f)", tostring(bestEnc), best5, bestA)
	end
	local reach, total = 0, 0
	for _, smp in samples do
		local size = 2 ^ smp.lsz
		for _, key in smp.keys do
			local sv = storedOf(key.p)
			if sv then
				total += 1
				local i = band(decodeHash(sv, (key.p + St.hash) % TWO32, bestEnc), size - 1)
				for _ = 1, 64 do
					if i == key.i then
						reach += 1
						break
					end
					local nx = b_u32(smp.nb, i * 32 + 28) // 16
					if nx >= 0x8000000 then nx -= 0x10000000 end
					if nx == 0 then break end
					i += nx
					if i < 0 or i >= size then break end
				end
			end
		end
	end
	if total < 50 or reach < total * 0.995 then
		return false, string.format("probe check failed: %d of %d keys reachable", reach, total)
	end
	St.hashEnc = bestEnc
	note(string.format("string hash: %s encoding (heads %.3f, big tables %.3f, probe check %d/%d)", bestEnc, bestA, best5, reach, total))
	return true
end

local function vmStatsLite(vm)
	local hb = rd(vm.G + vm.strt, 16)
	if hb then vm.strings = b_u32(hb, 8) end
end

local function classifyByStrings(vm, maxStrings)
	local hdr = rd(vm.G + vm.strt, 16)
	if not hdr then return nil end
	local h, size = q(hdr, 0), b_u32(hdr, 12)
	if not isptr(h) or size < 256 or band(size, size - 1) ~= 0 then return nil end
	maxStrings = maxStrings or 8000
	local slices = 32
	local per = math.max(1, math.min(256, size // slices))
	local seen, core, game = 0, 0, 0
	for sIdx = 0, slices - 1 do
		local bb = rd(h + ((size // slices) * sIdx) * 8, per * 8)
		if bb then
			for i = 0, per - 1 do
				local p = q(bb, i * 8)
				local guard = 0
				while isptr(p) and guard < 16 do
					guard += 1
					local sb = rd(p, 0x18 + 48)
					if not sb or b_u8(sb, 1) ~= vm.strTag then break end
					seen += 1
					local len = b_u32(sb, 0x14)
					if len >= 3 and len <= 0x10000 and b_u8(sb, 0x18) == 61 then
						if sourceKind(b_str(sb, 0x18, math.min(len, 48))) == "core" then core += 1 else game += 1 end
					end
					p = q(sb, 8)
				end
			end
		end
		if (core >= 12 and game * 10 <= core) or (game >= 12 and core * 10 <= game) or seen >= maxStrings then break end
	end
	vm.strCore, vm.strGame, vm.strSeen = core, game, seen
	local n = core + game
	if n < 6 then return nil end
	if core >= n * 0.6 then return "core" end
	if core * 10 <= n then return "game" end
	return nil
end

local Lazy = { state = {}, err = {}, failedAt = {}, census = nil, base = nil }

local function lazyCensus()
	if Lazy.census then return Lazy.census end
	local base = Lazy.base or Current
	local samples, counts, sizes, known, pages = sampleCensus(base, 600, 300)
	Lazy.census = { samples = samples, counts = counts, sizes = sizes, known = known, pages = pages, base = base }
	return Lazy.census
end

local function dominantSize(sizes, t)
	local best, bc = nil, 0
	for bs, c in sizes[t] or {} do
		if c > bc then best, bc = bs, c end
	end
	return best
end

local function lazyFunctions()
	local L = Layout
	local tags = rawget(L, "tags")
	local c = lazyCensus()
	local samples, known = c.samples, c.known
	local fnSamples = samples[tags.func] or {}
	if #fnSamples < 30 then error("too few function samples (" .. #fnSamples .. ")") end
	local cCount = 0
	for _, sm in fnSamples do
		for o = 0x10, math.min(b_len(sm.b), 0x40) - 8, 8 do
			if moduleRange(q(sm.b, o)) then
				cCount += 1
				break
			end
		end
	end
	if cCount < 8 then
		local extra = 0
		local order = {}
		for _, vm in VMs do order[#order + 1] = vm end
		table.sort(order, function(x, y) return (x.strings or 0) < (y.strings or 0) end)
		for _, vm in order do
			if extra >= 40 then break end
			forEachObject(vm, { [tags.func] = true }, function(addr, tt, buf, at, bsz)
				local span = math.min(bsz, 0x100, b_len(buf) - at)
				for o = 0x10, math.min(span, 0x40) - 8, 8 do
					if moduleRange(q(buf, at + o)) then
						local sb = b_create(span)
						b_copy(sb, 0, buf, at, span)
						fnSamples[#fnSamples + 1] = { a = addr, b = sb, bs = bsz }
						extra += 1
						break
					end
				end
				return extra >= 40
			end, newCtx({ MaxPages = 4000 }))
		end
	end
	local Cl, protoTag, nupP, stackP, uvTag = deriveClosure(fnSamples, tags, known)
	if not Cl then error(tostring(protoTag)) end
	pcall(function()
		local Th = rawget(L, "thread")
		local base = Lazy.base or Current
		if not Th or not Th.gt or not Cl.isC then return end
		local gt = readPtrAt(base.main + Th.gt, 0)
		local slot = isptr(gt) and findSlot(gt, "print", base)
		local vb = slot and rd(slot, 16)
		if not vb or b_i32(vb, 12) ~= tags.func then return end
		local fb = rd(q(vb, 0), 0x60)
		if not fb or b_u8(fb, Cl.isC) ~= 1 then return end
		local function nameAt(o)
			if not o or o + 8 > 0x60 then return nil end
			local ptr = q(fb, o)
			return isptr(ptr) and tsRead(ptr, 16) or nil
		end
		if nameAt(Cl.cName) == "print" then return end
		for o = 8, 0x58, 8 do
			if nameAt(o) == "print" then
				note(string.format("C closure name field corrected from %s to +0x%x (checked on print)", tostring(Cl.cName), o))
				Cl.cName = o
				return
			end
		end
	end)
	local P = rawget(L, "pages")
	local idx = pageIndex(c.base, "gc")
	local function topUp(tag, want, lo, hi)
		local list = samples[tag] or {}
		samples[tag] = list
		if not tag or #list >= want then return list end
		local have = {}
		for _, sm in list do have[sm.a] = true end
		local classes = {}
		for bs in c.sizes[tag] or {} do classes[#classes + 1] = bs end
		if #classes == 0 then
			for _, bs in idx.bsList do
				if bs >= lo and bs <= hi then classes[#classes + 1] = bs end
			end
		end
		for _, bs in classes do
			local plist = idx.byBs[bs] or {}
			local stride = math.max(1, #plist / math.ceil(want / 4))
			local fi = 1
			while fi <= #plist do
				if #list >= want then break end
				local e = plist[math.floor(fi)]
				fi += stride
				local buf = rd(e[1], e[2])
				local at, stop
				if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
				if at then
					local per = 0
					while at + 2 <= stop and #list < want and per < 4 do
						if b_u8(buf, at + 1) == tag then
							local addr = e[1] + at
							if not have[addr] then
								have[addr] = true
								per += 1
								local span = math.min(e[3], 0x100, b_len(buf) - at)
								local sb = b_create(span)
								b_copy(sb, 0, buf, at, span)
								list[#list + 1] = { a = addr, b = sb, bs = e[3] }
								known[addr] = tag
								c.sizes[tag] = c.sizes[tag] or {}
								c.sizes[tag][e[3]] = (c.sizes[tag][e[3]] or 0) + 1
							end
						end
						at += e[3]
					end
				end
			end
		end
		return list
	end
	local pSm = topUp(protoTag, 160, 160, 320)
	if uvTag then topUp(uvTag, 60, 24, 64) end
	if not pSm or #pSm < 30 then error("too few proto samples (" .. tostring(pSm and #pSm) .. ")") end
	for _, sm in pSm do sm.tagP = protoTag end
	local Pr, e3 = deriveProto(pSm, tags, known)
	if not Pr then error(tostring(e3)) end
	Pr.nups = nupP
	Pr.maxstack = stackP
	Pr.bs = dominantSize(c.sizes, protoTag)
	Pr.line = deriveProtoLine(pSm, Pr)
	local Up = nil
	if uvTag and samples[uvTag] then Up = deriveUpval(samples[uvTag]) end
	rawset(tags, "proto", protoTag)
	rawset(tags, "upval", uvTag)
	rawset(L, "closure", Cl)
	rawset(L, "proto", Pr)
	rawset(L, "upval", Up)
	Lazy.census = nil
	if not Pr.line then
		local base = c.base
		if pcall(classifyVM, base) and base.protoSamples and #base.protoSamples >= 20 then
			local okL, line = pcall(deriveProtoLine, base.protoSamples, Pr)
			if okL and line then Pr.line = line end
		end
		base.protoSamples = nil
	end
end

local function lazyUdata()
	local L = Layout
	local tags = rawget(L, "tags")
	local us0, uk0 = Lazy.usamples, Lazy.uknown
	Lazy.usamples, Lazy.uknown = nil, nil
	if us0 and #us0 >= 20 then
		local okU, U = pcall(deriveUdata, us0, tags, uk0)
		if okU and U then
			rawset(L, "udata", U)
			pcall(anchorInstance, VMs)
			if U.anchored then return end
			rawset(L, "udata", nil)
			note("userdata layout from attach samples did not anchor on game; using a census")
		end
	end
	local c = lazyCensus()
	local us = c.samples[tags.userdata]
	if not us or #us < 20 then
		rawset(L, "udata", nil)
		error("too few userdata samples")
	end
	local U = deriveUdata(us, tags, c.known)
	if not U then
		rawset(L, "udata", nil)
		error("userdata layout not derived")
	end
	rawset(L, "udata", U)
	pcall(anchorInstance, VMs)
	if not U.anchored then note("userdata layout derived but the game Instance anchor was not found") end
	if rawget(L, "closure") then Lazy.census = nil end
end

local function lazyThread()
	local L = Layout
	local tags = rawget(L, "tags")
	local base = Lazy.base or Current
	local Tt = tags.thread
	local P = L.pages
	local idx = pageIndex(base, "gc")
	local want = {}
	if base.main and base.G > base.main and base.G - base.main <= 0x400 then want[base.G - base.main] = true end
	local list, known, sizes = {}, {}, {}
	for bs in want do
		for _, e in idx.byBs[bs] or {} do
			if #list >= 60 then break end
			local buf = rd(e[1], e[2])
			local at, stop
			if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
			if at then
				while at + 2 <= stop and #list < 60 do
					if b_u8(buf, at + 1) == Tt then
						local addr = e[1] + at
						local span = math.min(e[3], 0x100, b_len(buf) - at)
						local sb = b_create(span)
						b_copy(sb, 0, buf, at, span)
						list[#list + 1] = { a = addr, b = sb, bs = e[3] }
						known[addr] = Tt
						sizes[e[3]] = (sizes[e[3]] or 0) + 1
					end
					at += e[3]
				end
			end
		end
	end
	if #list < 3 then
		local c = lazyCensus()
		list = c.samples[Tt] or {}
		known = c.known
		sizes = c.sizes[Tt] or {}
	end
	if #list < 3 then error("too few thread samples") end
	local Th = deriveThread(list, tags, known, L.lGlobal)
	if not Th then error("thread layout not derived") end
	local best, bc = nil, 0
	for bs, n in sizes do
		if n > bc then best, bc = bs, n end
	end
	Th.bs = best
	rawset(L, "thread", Th)
	pcall(validateNumberTag, VMs)
end

local function lazyGlobals()
	rawset(Layout, "globals", deriveGlobals(VMs))
end

local LazyGroup = { closure = "functions", proto = "functions", upval = "functions", udata = "udata", thread = "thread", globals = "globals" }
local LazyRun = { functions = lazyFunctions, udata = lazyUdata, thread = lazyThread, globals = lazyGlobals }

local LAZY_RETRY = 5

local function runLazy(L, group)
	if L ~= Layout then return end
	local st = Lazy.state[group]
	if st == "ok" then return end
	if st == "running" then
		if coroutine.isyieldable() and waitFn then
			local w0 = clock()
			while Lazy.state[group] == "running" and L == Layout and clock() - w0 < 30 do waitFn() end
		end
		return
	end
	if st == "failed" and clock() - (Lazy.failedAt[group] or 0) < LAZY_RETRY then return end
	Lazy.state[group] = "running"
	local t0 = clock()
	local ok, err = pcall(LazyRun[group])
	if L ~= Layout then return end
	if ok then
		Lazy.state[group] = "ok"
		Lazy.err[group] = nil
		note(string.format("%s layout derived in %.0f ms", group, (clock() - t0) * 1000))
	else
		Lazy.state[group] = "failed"
		Lazy.failedAt[group] = clock()
		Lazy.err[group] = tostring(err)
		note(group .. " layout failed: " .. tostring(err))
	end
end

ensureLazy = function(group)
	if not Layout or not Current then requireAttached() end
	local L = Layout
	if not L then return end
	runLazy(L, group)
	if Lazy.state[group] ~= "ok" then
		local why = Lazy.err[group] or Lazy.state[group] or "not derived"
		error("SevereGC: the " .. group .. " layout is not available (" .. tostring(why) .. "); try again in a few seconds", 3)
	end
end

local LayoutMeta = {
	__index = function(t, k)
		local g = LazyGroup[k]
		if g then
			runLazy(t, g)
			return rawget(t, k)
		end
		return nil
	end,
}

local TagsMeta = {
	__index = function(t, k)
		if k == "proto" or k == "upval" then
			local L = Layout
			if L and rawget(L, "tags") == t then
				runLazy(L, "functions")
				return rawget(t, k)
			end
		end
		return nil
	end,
}

local function deriveCore(list, base)
	local P, why = derivePages(base.G)
	if not P then return nil, why end
	local S, T = base.strTag, base.thrTag
	local tags = {
		["nil"] = 0, boolean = 1, lightuserdata = 2, number = 3, vector = 4,
		string = S, table = S + 1, func = S + 2, userdata = S + 3, thread = T,
	}
	Layout = {
		pages = P,
		tags = tags,
		str = { next = 8, hash = 0x10, len = 0x14, data = 0x18 },
		lGlobal = base.lGlobal,
		strt = base.strt,
		mainOff = base.mainOff,
	}
	Lazy = { state = {}, err = {}, failedAt = {}, census = nil, base = base }
	setmetatable(tags, TagsMeta)
	setmetatable(Layout, LayoutMeta)
	TagCache = {}
	TagCacheN = 0
	local idx = pageIndex(base, "gc", 0)
	local samples, known, perClass = {}, {}, {}
	local usamples = {}
	local TT, UT = tags.table, tags.userdata
	for _, bs in idx.bsList do
		if bs >= 32 and bs <= 128 then
			local plist = idx.byBs[bs]
			local stride = math.max(1, #plist // 6)
			local used = 0
			for pi = 1, #plist, stride do
				if used >= 6 then break end
				local e = plist[pi]
				local buf = rd(e[1], e[2])
				local at, stop
				if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
				if at then
					used += 1
					local per = 0
					while at + 2 <= stop do
						local tt = b_u8(buf, at + 1)
						if tt ~= 0 then
							local addr = e[1] + at
							known[addr] = tt
							if tt == TT then
								perClass[bs] = (perClass[bs] or 0) + 1
								if per < 8 and #samples < 240 then
									per += 1
									local span = math.min(bs, 0x100, b_len(buf) - at)
									local sb = b_create(span)
									b_copy(sb, 0, buf, at, span)
									samples[#samples + 1] = { a = addr, b = sb, bs = bs }
								end
							elseif tt == UT and #usamples < 400 then
								local span = math.min(bs, 0x100, b_len(buf) - at)
								local sb = b_create(span)
								b_copy(sb, 0, buf, at, span)
								usamples[#usamples + 1] = { a = addr, b = sb, bs = bs }
							end
						end
						at += bs
					end
				end
			end
		end
	end
	local bestBs, bestC = nil, 0
	for bs, n in perClass do
		if n > bestC then bestBs, bestC = bs, n end
	end
	if bestBs then
		local have = {}
		for _, sm in samples do have[sm.a] = true end
		local plist = idx.byBs[bestBs] or {}
		local stride = math.max(1, #plist // 16)
		for pi = 1, #plist, stride do
			if #samples >= 600 then break end
			local e = plist[pi]
			local buf = rd(e[1], e[2])
			local at, stop
			if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
			if at then
				local per = 0
				while at + 2 <= stop do
					local tt = b_u8(buf, at + 1)
					if tt ~= 0 then
						local addr = e[1] + at
						known[addr] = tt
						if tt == TT and not have[addr] and per < 40 and #samples < 600 then
							have[addr] = true
							per += 1
							local span = math.min(bestBs, 0x100, b_len(buf) - at)
							local sb = b_create(span)
							b_copy(sb, 0, buf, at, span)
							samples[#samples + 1] = { a = addr, b = sb, bs = bestBs }
						end
					end
					at += bestBs
				end
			end
		end
	end
	do
		local haveU = {}
		for _, sm in usamples do haveU[sm.a] = true end
		for _, bs in idx.bsList do
			if #usamples >= 700 then break end
			if bs >= 16 and bs <= 0x2000 then
				local plist = idx.byBs[bs] or {}
				local stride = math.max(1, #plist // 2)
				for pi = 1, #plist, stride do
					local e = plist[pi]
					if e[2] <= 0x10000 then
						local buf = rd(e[1], e[2])
						local at, stop
						if buf then at, stop = pageRange(buf, P, e[2], e[3]) end
						if at then
							local per = 0
							while at + 2 <= stop and per < 8 do
								local tt = b_u8(buf, at + 1)
								if tt ~= 0 then
									local addr = e[1] + at
									if known[addr] == nil then known[addr] = tt end
									if tt == UT and not haveU[addr] then
										haveU[addr] = true
										per += 1
										local span = math.min(e[3], 0x100, b_len(buf) - at)
										local sb = b_create(span)
										b_copy(sb, 0, buf, at, span)
										usamples[#usamples + 1] = { a = addr, b = sb, bs = e[3] }
									end
								end
								at += e[3]
							end
						end
					end
				end
			end
		end
	end
	if #samples < 30 then return nil, "too few table samples (" .. #samples .. ")" end
	local Tb, e1 = deriveTable(samples, tags, known)
	if not Tb then return nil, e1 end
	Tb.bs = bestBs
	local votes = {}
	for _, sm in samples do
		if Tb.node + 8 <= b_len(sm.b) and b_u8(sm.b, Tb.lsz) == 0 then
			local v = q(sm.b, Tb.node)
			if moduleRange(v) then votes[v] = (votes[v] or 0) + 1 end
		end
	end
	local bd, bv = nil, 0
	for v, n in votes do
		if n > bv then bd, bv = v, n end
	end
	if bd and bv >= 3 then Tb.dummy = bd end
	Layout.table = Tb
	Lazy.usamples, Lazy.uknown = usamples, known
	return Layout
end

local function finishCore(list, base)
	for i, vm in list do
		vm.index = i
		vmStatsLite(vm)
		if not vm.kind then
			local okK, k = pcall(classifyByStrings, vm)
			vm.kind = (okK and k) or "unknown"
		end
	end
	local order = { base }
	for _, vm in list do
		if vm ~= base then order[#order + 1] = vm end
	end
	for _, vm in order do
		local okH, res, why = pcall(deriveStrHash, vm)
		if okH and res then break end
		note("string hash not derived on VM " .. tostring(vm.index) .. ": " .. tostring(okH and why or res))
	end
	runLazy(Layout, "thread")
	runLazy(Layout, "udata")
end

function SevereGC.attach(which, opts)
	opts = opts or {}
	if not memRead then
		Status = "memory.readbuffer is missing"
		return false, Status
	end
	local sc0 = clock()
	local sc = scriptContext()
	if not sc then
		Status = "ScriptContext not found"
		return false, Status
	end
	local scMs = (clock() - sc0) * 1000
	local wantFull = opts.Full or (which ~= nil and which ~= "game")
	if opts.Rescan or #VMs == 0 or not Layout or (wantFull and VMsPartial) then
		local accept = nil
		if not wantFull then
			accept = function(vm)
				local okK, k = pcall(classifyByStrings, vm)
				if okK and k then vm.kind = k end
				vmStatsLite(vm)
				return vm.kind == "game" and (vm.strings or 0) >= 16000
			end
		end
		local list, accepted = discoverVMs(sc, { Accept = accept, Rescan = opts.Rescan })
		if #list == 0 then
			Status = "no Luau VM found under ScriptContext"
			return false, Status
		end
		local base
		for _, vm in list do
			vmStatsLite(vm)
			if not vm.kind then
				local okK, k = pcall(classifyByStrings, vm)
				if okK and k then vm.kind = k end
			end
			if vm.kind == "game" and (not base or (vm.strings or 0) > (base.strings or 0)) then base = vm end
		end
		if not base then
			for _, vm in list do
				if not base or (vm.strings or 0) > (base.strings or 0) then base = vm end
			end
		end
		note(string.format("attach: %d VM%s found, core layout from VM 0x%x (%s)", #list, #list == 1 and "" or "s", base.G, tostring(base.kind)))
		local L, why = deriveCore(list, base)
		if not L then
			Layout = nil
			Status = "layout derivation failed: " .. tostring(why)
			return false, Status
		end
		VMs = list
		VMsPartial = accepted ~= nil
		finishCore(VMs, base)
		note("attach: core layout ready")
	end
	if which == nil then
		Current = chooseDefault(VMs)
	else
		Current = resolveVM(which)
	end
	if not Current then
		Status = "requested VM not found"
		return false, Status
	end
	Status = string.format("attached to VM %d (%s), %d VMs", Current.index, tostring(Current.kind), #VMs)
	SevereGC.LastAttach = { ms = (clock() - sc0) * 1000, scMs = scMs, cached = false }
	return true, Current
end

function SevereGC.detach()
	for h in Locks do pcall(h.stop, h, true) end
	Layout, VMs, Current = nil, {}, nil
	Lazy = { state = {}, err = {}, failedAt = {}, census = nil, base = nil }
	VMsPartial = false
	ProxyCache = setmetatable({}, { __mode = "v" })
	AddrByText = {}
	TextByAddr = {}
	TextByAddrN = 0
	MemoTables = {}
	MemoCount = 0
	Status = "not attached"
end

function SevereGC.vms()
	local out = {}
	for i, vm in VMs do
		vmStats(vm)
		out[i] = {
			index = i,
			kind = vm.kind,
			G = vm.G,
			strings = vm.strings,
			bytes = vm.bytes,
			gameProtos = vm.gameProtos,
			coreProtos = vm.coreProtos,
			gcPages = vm.gcPages,
			sources = vm.sources,
			current = vm == Current,
		}
	end
	return out
end

function SevereGC.info()
	local out = { status = Status, version = SevereGC.Version, notes = Notes }
	if Layout then
		out.layout = Layout
		out.tags = Layout.tags
	end
	if Current then
		vmStats(Current)
		out.vm = { index = Current.index, kind = Current.kind, G = Current.G, strings = Current.strings, bytes = Current.bytes }
	end
	out.vms = SevereGC.vms()
	return out
end

function SevereGC.intern(strings, opts)
	requireAttached()
	if type(strings) == "string" then strings = { strings } end
	local r = resolveStrings(pickVM(opts), strings, newCtx(opts))
	local out = {}
	for k, v in r do out[k] = v or nil end
	return out
end

function SevereGC.install(env)
	env = env or getgenv and getgenv() or _G
	env.getgc = SevereGC.getgc
	env.filtergc = SevereGC.filtergc
	env.getsenv = SevereGC.getsenv
	env.getrenv = SevereGC.getrenv
	env.getscripts = SevereGC.getscripts
	env.getscriptclosure = SevereGC.getscriptclosure
	env.getupvalues = SevereGC.getupvalues
	env.getupvalue = SevereGC.getupvalue
	env.setupvalue = SevereGC.setupvalue
	env.getconstants = SevereGC.getconstants
	env.getconstant = SevereGC.getconstant
	env.setconstant = SevereGC.setconstant
	env.getprotos = SevereGC.getprotos
	env.getproto = SevereGC.getproto
	env.getinfo = SevereGC.getinfo
	env.getrawmetatable = SevereGC.getmetatable
	env.islclosure = function(f)
		local inf = infoOf(f)
		if not inf or inf.kind ~= "function" then return false end
		local _, isC = closureInfo(f)
		return not isC
	end
	env.iscclosure = function(f)
		local inf = infoOf(f)
		if not inf or inf.kind ~= "function" then return false end
		local _, isC = closureInfo(f)
		return isC
	end
	local dbg = {}
	if type(debug) == "table" then
		for k, v in debug do dbg[k] = v end
	end
	dbg.getupvalues = SevereGC.getupvalues
	dbg.getupvalue = SevereGC.getupvalue
	dbg.setupvalue = SevereGC.setupvalue
	dbg.getconstants = SevereGC.getconstants
	dbg.getconstant = SevereGC.getconstant
	dbg.setconstant = SevereGC.setconstant
	dbg.getprotos = SevereGC.getprotos
	dbg.getproto = SevereGC.getproto
	dbg.getinfo = function(f, ...)
		if infoOf(f) then return SevereGC.getinfo(f) end
		return debug.info and debug.info(f, ...) or nil
	end
	env.debug = dbg
	return env
end

SevereGC._internal = {
	scriptContext = scriptContext,
	discoverVMs = discoverVMs,
	probeVM = probeVM,
	derivePages = derivePages,
	sampleCensus = sampleCensus,
	deriveTable = deriveTable,
	deriveClosure = deriveClosure,
	deriveProto = deriveProto,
	deriveUdata = deriveUdata,
	deriveThread = deriveThread,
	forEachObject = forEachObject,
	listPages = listPages,
	pageRange = pageRange,
	pageIsMeta = pageIsMeta,
	getLayout = function() return Layout end,
	setLayout = function(L) Layout = L end,
	moduleRange = moduleRange,
	rd = rd,
	q = q,
	isptr = isptr,
	deriveStrHash = deriveStrHash,
	stringHash = stringHash,
	probeNode = probeNode,
	decodeHash = decodeHash,
	pageIndex = pageIndex,
	classifyFast = classifyFast,
}

return SevereGC
