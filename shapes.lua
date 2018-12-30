--[[
Copyright (c) 2011 Matthias Richter

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.
Except as contained in this notice, the name(s) of the above copyright holders
shall not be used in advertising or otherwise to promote the sale, use or
other dealings in this Software without prior written authorization.


THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
]]--

local math_min, math_max, math_abs, math_sqrt, math_huge, math_cos, math_sin, math_tau = math.min, math.max, math.abs, math.sqrt, math.huge, math.cos, math.sin, math.tau or math.pi * 2
local table_insert, table_remove, table_sort = table.insert, table.remove, table.sort

local _PACKAGE, common_local = (...):match("^(.+)%.[^%.]+"), common
if not (type(common) == 'table' and common.class and common.instance) then
	assert(common_class ~= false, 'No class commons specification available.')
	require(_PACKAGE .. '.class')
end
local vector  = require(_PACKAGE .. '.vector-light')
local GJK     = require(_PACKAGE .. '.gjk') -- actual collision detection

-- reset global table `common' (required by class commons)
if common_local ~= common then
	common_local, common = common, common_local
end

----------------------------
-- Private helper functions for polygons
--

local vertexMetatable = {
	__index = function(table, key)
		if key == "x" or key == "y" then
			local x, y
			x, y = table.owner:getCoordinates(rawget(table, "rx"), rawget(table, "ry"))
			return key == "x" and x or key == "y" and y
		end
		return rawget(table, key)
	end,
	__newindex = function(table, key, value)
		if key == "x" or key == "y" or key == "rx" or key == "ry" then
			error("Thou shalt not change a polygon's vertices!")
		end
		return rawset(table, key, value)
	end
}

-- create vertex list of coordinate pairs
local function toVertexList(owner, vertices, x,y, ...)
	if not (x and y) then return vertices end -- no more arguments

	vertices[#vertices + 1] = setmetatable({owner = owner, rx = x, ry = y}, vertexMetatable)   -- set vertex
	return toVertexList(owner, vertices, ...)         -- recurse
end

-- returns true if three vertices lie on a line
local function areCollinear(p, q, r, sameTransform, eps)
	return (sameTransform and math_abs(vector.det(q.rx-p.rx, q.ry-p.ry,  r.rx-p.rx,r.ry-p.ry)) or math_abs(vector.det(q.x-p.x, q.y-p.y,  r.x-p.x,r.y-p.y))) <= (eps or 1e-32)
end
-- remove vertices that lie on a line
local function removeCollinear(vertices, sameTransform)
	local ret = {}
	local i,k = #vertices - 1, #vertices
	for l=1,#vertices do
		if not areCollinear(vertices[i], vertices[k], vertices[l], sameTransform) then
			ret[#ret+1] = vertices[k]
		end
		i,k = k,l
	end
	return ret
end

-- get index of rightmost vertex (for testing orientation)
local function getIndexOfleftmost(vertices, sameTransform)
	local idx = 1
	for i = 2,#vertices do
		if (sameTransform and vertices[i].rx or vertices[i].x) < (sameTransform and vertices[idx].rx or vertices[idx].x) then
			idx = i
		end
	end
	return idx
end

-- returns true if three points make a counter clockwise turn
local function ccw(p, q, r, sameTransform)
	return (sameTransform and vector.det(q.rx-p.rx, q.ry-p.ry,  r.rx-p.rx, r.ry-p.ry) or vector.det(q.x-p.x, q.y-p.y,  r.x-p.x, r.y-p.y)) >= 0
end

-- test wether a and b lie on the same side of the line c->d
local function onSameSide(a,b, c,d, sameTransform)
	local dx, cx, dy, cy, ax, bx, ay, by
	if sameTransform then
		dx, cx, dy, cy, ax, bx, ay, by = d.rx, c.rx, d.ry, c.ry, a.rx, b.rx, a.ry, b.ry
	else
		dx, cx, dy, cy, ax, bx, ay, by = d.x, c.x, d.y, c.y, a.x, b.x, a.y, b.y
	end

	local px, py = dx-cx, dy-cy
	local l = vector.det(px,py,  ax-cx, ay-cy)
	local m = vector.det(px,py,  bx-cx, by-cy)
	return l*m >= 0
end

local function pointInTriangle(p, a,b,c, sameTransform)
	return onSameSide(p,a, b,c, sameTransform) and onSameSide(p,b, a,c, sameTransform) and onSameSide(p,c, a,b, sameTransform)
end

-- test whether any point in vertices (but pqr) lies in the triangle pqr
-- note: vertices is *set*, not a list!
local function anyPointInTriangle(vertices, p,q,r, sameTransform)
	for v in pairs(vertices) do
		if v ~= p and v ~= q and v ~= r and pointInTriangle(v, p,q,r, sameTransform) then
			return true
		end
	end
	return false
end

-- test is the triangle pqr is an "ear" of the polygon
-- note: vertices is *set*, not a list!
local function isEar(p,q,r, vertices, sameTransform)
	return ccw(p,q,r) and not anyPointInTriangle(vertices, p,q,r, sameTransform)
end

local function segmentsIntersect(a,b, p,q, sameTransform)
	return not (onSameSide(a,b, p,q, sameTransform) or onSameSide(p,q, a,b, sameTransform))
end

-- returns starting/ending indices of shared edge, i.e. if p and q share the
-- edge with indices p1,p2 of p and q1,q2 of q, the return value is p1,q2
local function getSharedEdge(p,q, sameTransform)
	local pindex = setmetatable({}, {__index = function(t,k)
		local s = {}
		t[k] = s
		return s
	end})

	-- record indices of vertices in p by their coordinates
	for i = 1,#p do
		pindex[sameTransform and p[i].rx or p[i].x][sameTransform and p[i].rx or p[i].y] = i
	end

	-- iterate over all edges in q. if both endpoints of that
	-- edge are in p as well, return the indices of the starting
	-- vertex
	local i,k = #q,1
	for k = 1,#q do
		local v,w = q[i], q[k]
		if pindex[sameTransform and v.rx or v.x][sameTransform and v.rx or v.y] and pindex[sameTransform and w.rx or w.x][sameTransform and w.ry or w.y] then
			return pindex[sameTransform and w.rx or w.x][sameTransform and w.ry or w.y], k
		end
		i = k
	end
end



--
-- base class
--
local Shape = {}
function Shape:init(t, x, y, r, s, o)
	self.type = t
	self.tx = x or 0
	self.ty = y or 0
	self.r = r or 0
	self.s = s or 1
	self.origin = o
	self.owningHashes = {}
	self.children = {}
	self.cachedBbox = {}
	self.cachedAnswers = {}
	self.stack = {}
	if o then o.children[self] = true end
end

local function getTransformedCoordinates(x, y, tx, ty, r, s)
	x, y = x or 0, y or 0
	x, y = x * s, y * s
	local c, s = math_cos(r), math_sin(r)
	x, y = x * c - y * s, y * c + x * s
	x, y = x + tx, y + ty
	return x, y
end

local function getTransformedTransform(starttx, startty, startr, starts, newtx, newty, newr, news)
	local cosine, sine = math_cos(startr), math_sin(startr)
	return
		starttx + starts * newtx * cosine - starts * newty * sine,
		startty + starts * newty * cosine + starts * newtx * sine,
		(startr + newr) % math_tau,
		starts * news
end

local function getRequiredTransform(starttx, startty, startr, starts, desttx, destty, destr, dests)
	-- such that getTransformedTransform(starttx,startty,startr,starts,getRequiredTransform(starttx, startty, startr, starts, desttx, destty, destr, dests) is desttx,destty,destr,dests
	-- so yeah it's getTransformedTransform's inverse
	-- this function was from Positive07 on the LÖVE discord. cheers!!
	local tx = desttx - starttx
	local ty = destty - startty
	local sine   = math_sin(startr) / starts
	local cosine = math_cos(startr) / starts

	return
		tx * cosine + ty * sine,
		ty * cosine - tx * sine,
		destr - startr,
		dests / starts
end

function Shape:getCoordinates(x, y)
	local cachedAnswers = self.cachedAnswers
	cachedAnswers.x, cachedAnswers.y = cachedAnswers.x or {}, cachedAnswers.y or {}
	if cachedAnswers.x[x] and cachedAnswers.y[y] then return cachedAnswers.x[x] and cachedAnswers.y[y] end
	return getTransformedCoordinates(x, y, self:getAbsoluteTransform())
end

function Shape:getAbsoluteTransform()
	if self.cachedAnswers.transform then return unpack(self.cachedAnswers.transform) end
	if self.origin then
		local ortx, orty, orr, ors = self.origin:getAbsoluteTransform()
		local tttx, ttty, ttr, tts = getTransformedTransform(ortx, orty, orr, ors, self:getRelativeTransform())
		self.cachedAnswers.transform = {tttx, ttty, ttr, tts}
		return tttx, ttty, ttr, tts
	else
		return self:getRelativeTransform()
	end
end

function Shape:setAbsoluteTransform(tx, ty, r, s)
	self:cacheBboxes()
	if self.origin then
		local tx2, ty2, r2, s2 = self.origin:getAbsoluteTransform()
		self:setRelativeTransform(getRequiredTransform(tx2, ty2, r2, s2, tx, ty, r, s))
	else
		self:setRelativeTransform(tx, ty, r, s)
	end
	return self:doUpdates()
end

function Shape:getRelativeTransform()
	return self.tx, self.ty, self.r, self.s
end

function Shape:setRelativeTransform(tx, ty, r, s)
	self:cacheBboxes()
	self.tx, self.ty, self.r, self.s = tx, ty, r, s
	return self:doUpdates()
end

function Shape:push()
	local copy = {self:getRelativeTransform()}
	table_insert(self.stack, copy)
	return self
end

function Shape:pop()
	self:cacheBboxes()
	local removed = table.remove(self.stack)
	self:setRelativeTransform(unpack(removed))
	return self:doUpdates()
end

function Shape:translate(x, y)
	self:cacheBboxes()
	self.tx, self.ty = self.tx + x, self.ty + y
	return self:doUpdates()
end

function Shape:translateTo(x, y)
	self:cacheBboxes()
	self.tx, self.ty = x, y
	return self:doUpdates()
end

function Shape:rotate(angle)
	self:cacheBboxes()
	self.r = self.r + angle
	return self:doUpdates()
end

function Shape:rotateTo(angle)
	self:cacheBboxes()
	self.r = angle
	return self:doUpdates()
end

function Shape:scale(amount)
	self:cacheBboxes()
	self.s = self.s * amount
	return self:doUpdates()
end

function Shape:scaleTo(amount)
	self:cacheBboxes()
	self.s = amount
	return self:doUpdates()
end

function Shape:setRelativeTo(shape, dontKeepAbsoluteTransform)
	if not shape then
		local tx, ty, r, s = self:getAbsoluteTransform()
		if self.origin then
			self.origin.children[self] = nil
		end
		self.origin = nil
		return self:setRelativeTransform(tx, ty, r, s)
	else
		local tx, ty, r, s
		if dontKeepAbsoluteTransform then
			self:cacheBboxes()
		else -- getAbsoluteTransform already does cacheBboxes()
			tx, ty, r, s = self:getAbsoluteTransform()
		end
		if self.origin then
			self.origin.children[self] = nil
		end
		if shape then
			shape.children[self] = true
		end
		self.origin = shape
		if dontKeepAbsoluteTransform then
			return self:doUpdates()
		else -- setAbsoluteTransform already calls doUpdates
			return self:setAbsoluteTransform(tx, ty, r, s)
		end
	end
end

function Shape:doUpdates()
	self.cachedAnswers.x, self.cachedAnswers.y, self.cachedAnswers.transform = nil
	for hash in pairs(self.owningHashes) do
		hash:update(self, self.cachedBbox[1], self.cachedBbox[2], self.cachedBbox[3], self.cachedBbox[4], self:bbox())
	end
	for shape in pairs(self.children) do
		shape:doUpdates()
	end
	return self
end

function Shape:cacheBboxes()
	self.cachedBbox[1], self.cachedBbox[2], self.cachedBbox[3], self.cachedBbox[4] = self:bbox()
	for shape in pairs(self.children) do
		shape:cacheBboxes()
	end
	return self
end

function Shape:intersectionsWithSegment(x1, y1, x2, y2)
	local dx, dy = x2-x1,y2-y1

	if dx == 0 and dy == 0 then
		if self:contains(x1, y1) then
			return {0}
		else
			return {}
		end
	end

	local intersections = self:intersectionsWithRay(x1,y1,dx,dy)

	local i = 1
	while i <= #intersections do
		local parameter = intersections[i]
		if parameter < 0 or parameter > 1 then
			table_remove(intersections, i)
		else
			i = i + 1
		end
	end

	return intersections
end

function Shape:segmentIntersectionLength(x1,y1, x2,y2)
	local intersections = self:intersectionsWithSegment(x1,y1, x2,y2)
	if listLength == 0 then return 0 end
	local dx, dy = x2-x1,y2-y1
	local function contains(p, q)
		p = q and (p + q) / 2 or p
		return self:contains(x1 + dx * p, y1 + dy * p)
	end
	if contains(0) then
		table_insert(intersections, 0)
	end
	if contains(1) then
		table_insert(intersections, 1)
	end	
	table_sort(intersections)
	local listLength = #intersections
	
	local ret = 0
	for i = 1, listLength - 1 do
		local a, b = intersections[i], intersections[i + 1]
		if contains(a, b) then ret = ret + b - a end
	end
	return ret * math_sqrt(dx^2+dy^2)
end

--
-- class definitions
--
local PolygonShape = {}
function PolygonShape:init(origin, master, ...)
	self.masterPolygon = master
	Shape.init(self, 'polygon', nil,nil,nil,nil, origin)
	local vertices = removeCollinear( toVertexList(self, {}, ...) )
	assert(#vertices >= 3, "Need at least 3 non collinear points to build polygon (got "..#vertices..")")

	-- assert polygon is oriented counter clockwise
	local r = getIndexOfleftmost(vertices)
	local q = r > 1 and r - 1 or #vertices
	local s = r < #vertices and r + 1 or 1
	if not ccw(vertices[q], vertices[r], vertices[s]) then -- reverse order if polygon is not ccw
		local tmp = {}
		for i=#vertices,1,-1 do
			tmp[#tmp + 1] = vertices[i]
		end
		vertices = tmp
	end

	-- assert polygon is not self-intersecting
	-- outer: only need to check segments #vert;1, 1;2, ..., #vert-3;#vert-2
	-- inner: only need to check unconnected segments
	local q,p = vertices[#vertices]
	for i = 1,#vertices-2 do
		p, q = q, vertices[i]
		for k = i+1,#vertices-1 do
			local a,b = vertices[k], vertices[k+1]
			assert(not segmentsIntersect(p,q, a,b), 'Polygon may not intersect itself')
		end
	end
	self.vertices = vertices

	-- compute polygon area and centroid
	local p,q = vertices[#vertices], vertices[1]
	local det = vector.det(p.rx,p.ry, q.rx,q.ry) -- also used below
	self.area = det
	for i = 2,#vertices do
		p,q = q,vertices[i]
		self.area = self.area + vector.det(p.rx,p.ry, q.rx,q.ry)
	end
	self.area = self.area / 2


	if not self.masterPolygon then
		p,q = vertices[#vertices], vertices[1]
		local centroidX, centroidY = (p.rx+q.rx)*det, (p.ry+q.ry)*det
		for i = 2,#vertices do
			p,q = q,vertices[i]
			det = vector.det(p.rx,p.ry, q.rx,q.ry)
			centroidX = centroidX + (p.rx+q.rx) * det
			centroidY = centroidY + (p.ry+q.ry) * det
		end
		centroidX = centroidX / (6 * self.area)
		centroidY = centroidY / (6 * self.area)
		self:translate(centroidX, centroidY)

		-- make vertices relative to centroid without changing their absolute position.
		for _, v in ipairs(vertices) do
			v.rx, v.ry = v.rx - centroidX, v.ry - centroidY
		end
	end

	-- get outcircle
	self.radius = 0
	for i = 1,#vertices do
		self.radius = math_max(self.radius,
			vector.dist(vertices[i].rx,vertices[i].ry, 0, 0))
	end

	-- make vertices immutable
	setmetatable(self.vertices, {__newindex = function() error("Thou shalt not change a polygon's vertices!") end})

	if not self.masterPolygon and not self:isConvex() then
		self.convexParts = self:splitConvex()
	end
end

local CircleShape = {}
function CircleShape:init(radius, x,y,r,s, origin)
	Shape.init(self, 'circle', x,y,r,s, origin)
	self.radius = radius
end

local PointShape = {}
function PointShape:init(x,y,r,s, origin)
	Shape.init(self, 'point', x,y,r,s, origin)
end

--
-- collision functions
--

function CircleShape:support(dx,dy)
	local x, y = self:getCoordinates()
	return vector.add(x, y,
		vector.mul(self:getRadius(), vector.normalize(dx,dy)))
end

-- collision dispatching:
-- let circle shape or compound shape handle the collision
function PolygonShape:collidesWith(other)
	if self == other then return false end
	if self:isConvex() then
		if other.type ~= 'polygon' then
			local collide, sx,sy = other:collidesWith(self)
			return collide, sx and -sx, sy and -sy
		end

		-- else: type is POLYGON
		return GJK(self, other)
	else
		if other.type == 'point' then
			return other:collidesWith(self)
		end

		-- TODO: better way of doing this. report all the separations?
		local collide,dx,dy = false,0,0
		for _,s in ipairs(self.convexParts) do
			local status, sx,sy = s:collidesWith(other)
			collide = collide or status
			if status then
				if math_abs(dx) < math_abs(sx) then
					dx = sx
				end
				if math_abs(dy) < math_abs(sy) then
					dy = sy
				end
			end
		end
		return collide, dx, dy
	end
end

function CircleShape:collidesWith(other)
	if self == other then return false end
	local selfx, selfy = self:getCoordinates()
	local otherx, othery = self:getCoordinates()
	if other.type == 'circle' then
		local px,py = selfx-otherx, selfy-othery
		local d = vector.len2(px,py)
		local radii = self:getRadius() + other:getRadius()
		if d < radii*radii then
			-- if circles overlap, push it out upwards
			if d == 0 then return true, 0,radii end
			-- otherwise push out in best direction
			return true, vector.mul(radii - math_sqrt(d), vector.normalize(px,py))
		end
		return false
	elseif other.type == 'polygon' then
		return GJK(self, other)
	end

	-- else: let the other shape decide
	local collide, sx,sy = other:collidesWith(self)
	return collide, sx and -sx, sy and -sy
end

function PointShape:collidesWith(other)
	if self == other then return false end
	local selfx, selfy = self:getCoordinates()
	local otherx, othery = other:getCoordinates()
	if other.type == 'point' then
		return (selfx == otherx and selfy == othery), 0,0
	end
	return other:contains(selfx, selfy), 0,0
end

--
-- point location/ray intersection
--
function CircleShape:contains(x,y)
	local selfx, selfy = self:getCoordinates()
	return vector.len2(x-selfx, y-selfy) < self:getRadius() ^ 2
end

function PointShape:contains(x,y)
	local selfx, selfy = self:getCoordinates()
	return x == selfx and y == selfy
end

-- circle intersection if distance of ray/center is smaller
-- than radius.
-- with r(s) = p + d*s = (x,y) + (dx,dy) * s defining the ray and
-- (x - cx)^2 + (y - cy)^2 = r^2, this problem is eqivalent to
-- solving [with c = (cx,cy)]:
--
--     d*d s^2 + 2 d*(p-c) s + (p-c)*(p-c)-r^2 = 0
function CircleShape:intersectionsWithRay(x,y, dx,dy)
	local selfx, selfy = self:getCoordinates()
	local pcx,pcy = x-selfx, y-selfy

	local a = vector.len2(dx,dy)
	local b = 2 * vector.dot(dx,dy, pcx,pcy)
	local c = vector.len2(pcx,pcy) - self:getRadius() ^ 2
	local discr = b*b - 4*a*c

	if discr < 0 then return {} end

	discr = math_sqrt(discr)
	local ts, t1, t2 = {}, discr-b, -discr-b
	if t1 >= 0 then ts[#ts+1] = t1/(2*a) end
	if t2 >= 0 then ts[#ts+1] = t2/(2*a) end
	return ts
end

function CircleShape:intersectsRay(x,y, dx,dy)
	local tmin = math_huge
	for _, t in ipairs(self:intersectionsWithRay(x,y,dx,dy)) do
		tmin = math_min(t, tmin)
	end
	return tmin ~= math_huge, tmin
end

-- point shape intersects ray if it lies on the ray
function PointShape:intersectsRay(x,y, dx,dy)
	local selfx, selfy = self:getCoordinates()
	local px,py = selfx-x, selfy-y
	local t = px/dx
	-- see (px,py) and (dx,dy) point in same direction
	return (t == py/dy), t
end

function PointShape:intersectionsWithRay(x,y, dx,dy)
	local intersects, t = self:intersectsRay(x,y, dx,dy)
	return intersects and {t} or {}
end

--
-- auxiliary
--
function PolygonShape:getRadius()
	return self.radius * self.s
end

function CircleShape:getRadius()
	return math_abs(self.radius * self.s)
end

function PointShape:getRadius()
	return 0
end

function PolygonShape:outcircle()
	local cx,cy = self:getCoordinates()
	return cx,cy, self:getRadius()
end

function CircleShape:outcircle()
	local cx,cy = self:getCoordinates()
	return cx,cy, self:getRadius()
end

function PointShape:outcircle()
	local x, y = self:getCoordinates()
	return x, y, 0
end

function CircleShape:bbox()
	local cx,cy = self:getCoordinates()
	local r = self:getRadius()
	return cx-r,cy-r, cx+r,cy+r
end

function PointShape:bbox()
	local x,y = self:getCoordinates()
	return x,y,x,y
end


function PolygonShape:draw(mode, wireframe)
	local mode = mode or 'line'
	if self:isConvex() then
		love.graphics.polygon(mode, self:unpackCoordinates())
	else
		if mode == 'line' then
			love.graphics.polygon('line', self:unpackCoordinates())
			if not wireframe then return end
		end
		for _,p in ipairs(self.convexParts) do
			love.graphics.polygon(mode, p:unpackCoordinates())
		end
	end
end

function CircleShape:draw(mode, segments)
	local x, y, r = self:outcircle()
	love.graphics.circle(mode or 'line', x, y, r, segments)
end

function PointShape:draw()
	love.graphics.points(self:getCoordinates())
end

-- original polygon.lua
-----------------
-- Polygon class
--

-- return vertices as x1,y1,x2,y2, ..., xn,yn
function PolygonShape:unpackCoordinates(sameTransform)
	local v = {}
	for i = 1,#self.vertices do
		v[2*i-1] = sameTransform and self.vertices[i].rx or self.vertices[i].x
		v[2*i]   = sameTransform and self.vertices[i].ry or self.vertices[i].y
	end
	return unpack(v)
end

-- deep copy of the polygon
local table_deepcopy = table.deepcopy or require(_PACKAGE .. ".deepcopy")
local parameters = {function_immutable = true, metatable_immutable = true}
function PolygonShape:clone()
	return table_deepcopy(self, parameters)
end

-- get bounding box
function PolygonShape:bbox()
	local ulx,uly = self.vertices[1].x, self.vertices[1].y
	local lrx,lry = ulx,uly
	for i=2,#self.vertices do
		local p = self.vertices[i]
		if ulx > p.x then ulx = p.x end
		if uly > p.y then uly = p.y end

		if lrx < p.x then lrx = p.x end
		if lry < p.y then lry = p.y end
	end

	return ulx,uly, lrx,lry
end

function PolygonShape:getRadius()
	return self.radius * self.s
end

-- a polygon is convex if all edges are oriented ccw
function PolygonShape:isConvex()
	local function isConvex()
		local v = self.vertices
		if #v == 3 then return true end

		if not ccw(v[#v], v[1], v[2], true) then
			return false
		end
		for i = 2,#v-1 do
			if not ccw(v[i-1], v[i], v[i+1], true) then
				return false
			end
		end
		if not ccw(v[#v-1], v[#v], v[1], true) then
			return false
		end
		return true
	end

	-- replace function so that this will only be computed once
	local status = isConvex()
	self.isConvex = function() return status end
	return status
end

-- triangulation by the method of kong
function PolygonShape:triangulate()
	if #self.vertices == 3 then return {self:clone()} end

	local vertices = self.vertices

	local next_idx, prev_idx = {}, {}
	for i = 1,#vertices do
		next_idx[i], prev_idx[i] = i+1,i-1
	end
	next_idx[#next_idx], prev_idx[1] = 1, #prev_idx

	local concave = {}
	for i, v in ipairs(vertices) do
		if not ccw(vertices[prev_idx[i]], v, vertices[next_idx[i]], true) then
			concave[v] = true
		end
	end

	local triangles = {}
	local n_vert, current, skipped, next, prev = #vertices, 1, 0
	while n_vert > 3 do
		next, prev = next_idx[current], prev_idx[current]
		local p,q,r = vertices[prev], vertices[current], vertices[next]
		if isEar(p,q,r, concave, true) then
			if not areCollinear(p, q, r, true) then
				triangles[#triangles+1] = common_local.instance(PolygonShape, self, self, p.rx,p.ry, q.rx,q.ry, r.rx,r.ry)
				next_idx[prev], prev_idx[next] = next, prev
				concave[q] = nil
				n_vert, skipped = n_vert - 1, 0
			end
		else
			skipped = skipped + 1
			assert(skipped <= n_vert, "Cannot triangulate polygon")
		end
		current = next
	end

	next, prev = next_idx[current], prev_idx[current]
	local p,q,r = vertices[prev], vertices[current], vertices[next]
	triangles[#triangles+1] = common_local.instance(PolygonShape, self, self, p.rx,p.ry, q.rx,q.ry, r.rx,r.ry)
	return triangles
end

-- return merged polygon if possible or nil otherwise
function PolygonShape:mergedWith(other, sameTransform)
	local justUnsplitting
	if self.masterPolygon and self.masterPolygon == other.masterPolygon then
		justUnsplitting = true
		sameTransform = true
	end
	local p,q = getSharedEdge(self.vertices, other.vertices)
	assert(p and q, "Polygons do not share an edge")

	local ret = {}
	for i = 1,p-1 do
		ret[#ret+1] = sameTransform and self.vertices[i].rx or self.vertices[i].x
		ret[#ret+1] = sameTransform and self.vertices[i].ry or self.vertices[i].y
	end

	for i = 0,#other.vertices-2 do
		i = ((i-1 + q) % #other.vertices) + 1
		ret[#ret+1] = sameTransform and other.vertices[i].rx or other.vertices[i].x
		ret[#ret+1] = sameTransform and other.vertices[i].ry or other.vertices[i].y
	end

	for i = p+1,#self.vertices do
		ret[#ret+1] = sameTransform and self.vertices[i].rx or self.vertices[i].x
		ret[#ret+1] = sameTransform and self.vertices[i].ry or self.vertices[i].y
	end

	table_insert(ret, justUnsplitting and self.masterPolygon)
	local new = common_local.instance(PolygonShape, sameTransform and self.origin, justUnsplitting and self.masterPolygon, unpack(ret))
	if sameTransform then
		new:setRelativeTransform(self:getRelativeTransform())
	end
	return new
end

-- split polygon into convex polygons.
-- note that this won't be the optimal split in most cases, as
-- finding the optimal split is a really hard problem.
-- the method is to first triangulate and then greedily merge
-- the triangles.
function PolygonShape:splitConvex()
	-- edge case: polygon is a triangle or already convex
	if #self.vertices <= 3 or self:isConvex() then return {self:clone()} end

	local convex = self:triangulate()
	local i = 1

	repeat
		local p = convex[i]
		local k = i + 1
		while k <= #convex do
			local success, merged = pcall(function() return p:mergedWith(convex[k], true) end)
			if success and merged:isConvex() then
				convex[i] = merged
				p = convex[i]
				table.remove(convex, k)
			else
				k = k + 1
			end
		end
		i = i + 1
	until i >= #convex

	return convex
end

function PolygonShape:contains(x,y)
	-- test if an edge cuts the ray
	local function cut_ray(p,q)
		return ((p.y > y and q.y < y) or (p.y < y and q.y > y)) -- possible cut
			and (x - p.x < (y - p.y) * (q.x - p.x) / (q.y - p.y)) -- x < cut.x
	end

	-- test if the ray crosses boundary from interior to exterior.
	-- this is needed due to edge cases, when the ray passes through
	-- polygon corners
	local function cross_boundary(p,q)
		return (p.y == y and p.x > x and q.y < y)
			or (q.y == y and q.x > x and p.y < y)
	end

	local v = self.vertices
	local in_polygon = false
	local p,q = v[#v],v[#v]
	for i = 1, #v do
		p,q = q,v[i]
		if cut_ray(p,q) or cross_boundary(p,q) then
			in_polygon = not in_polygon
		end
	end
	return in_polygon
end

function PolygonShape:intersectionsWithRay(x,y, dx,dy)
	if dx == 0 and dy == 0 then
		return {}
	end

	local nx,ny = vector.perpendicular(dx,dy)
	local wx,wy,det

	local ts = {} -- ray parameters of each intersection
	local q1,q2 = nil, self.vertices[#self.vertices]
	for i = 1, #self.vertices do
		q1,q2 = q2,self.vertices[i]
		wx,wy = q2.x - q1.x, q2.y - q1.y
		det = vector.det(dx,dy, wx,wy)

		if det ~= 0 then
			-- there is an intersection point. check if it lies on both
			-- the ray and the segment.
			local rx,ry = q2.x - x, q2.y - y
			local l = vector.det(rx,ry, wx,wy) / det
			local m = vector.det(dx,dy, rx,ry) / det
			if m >= 0 and m <= 1 then
				-- we cannot jump out early here (i.e. when l > tmin) because
				-- the polygon might be concave
				table_insert(ts, l)
			end
		else
			-- lines parralel or incident. get distance of line to
			-- anchor point. if they are incident, check if an endpoint
			-- lies on the ray
			local dist = vector.dot(q1.x-x,q1.y-y, nx,ny)
			if dist == 0 then
				local l = vector.dot(dx,dy, q1.x-x,q1.y-y)
				local m = vector.dot(dx,dy, q2.x-x,q2.y-y)
				table_insert(ts, math_max(l, m))
			end
		end
	end

	return ts
end

function PolygonShape:intersectsRay(x,y, dx,dy)
	local tmin = math_huge
	for _, t in ipairs(self:intersectionsWithRay(x,y,dx,dy)) do
		tmin = math_min(tmin, t)
	end
	return tmin ~= math_huge, tmin
end

function PolygonShape:support(dx,dy)
	local v = self.vertices
	local max, vmax = -math_huge
	for i = 1,#v do
		local d = vector.dot(v[i].x,v[i].y, dx,dy)
		if d > max then
			max, vmax = d, v[i]
		end
	end
	return vmax.x, vmax.y
end



Shape = common_local.class('Shape', Shape)
PolygonShape        = common_local.class('PolygonShape',        PolygonShape,        Shape)
CircleShape         = common_local.class('CircleShape',         CircleShape,         Shape)
PointShape          = common_local.class('PointShape',          PointShape,          Shape)

local function newPolygonShape(...)
	local origin
	local last = select(select("#", ...), ...)
	if last and type(last) ~= "number" then
		origin = last
	end
	return common_local.instance(PolygonShape, origin, nil, ...)
end

local function newCircleShape(...)
	return common_local.instance(CircleShape, ...)
end

local function newPointShape(...)
	return common_local.instance(PointShape, ...)
end

return {
	PolygonShape        = PolygonShape,
	CircleShape         = CircleShape,
	PointShape          = PointShape,
	newPolygonShape     = newPolygonShape,
	newCircleShape      = newCircleShape,
	newPointShape       = newPointShape
}
