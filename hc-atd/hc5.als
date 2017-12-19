module hc5	-- version 0.05

open util/boolean
open util/ordering[State] as so		-- state ordering
open util/ordering[Moment] as mo	-- moment ordering

sig State {}
sig Moment {}
abstract sig Vertex {
	left: lone Vertex,
	right: lone Vertex,
	momentLeft: Moment one -> State,
	momentRight: Moment one -> State,
	carryLeft: Bool one -> State,
	carryRight: Bool one -> State
}
sig Joint extends Vertex {}
sig End extends Vertex {}


----------- Connectivity Section -----------

-- All ends must only be connected right or left
fact {
	all e: End |
		(e.left = none and e = e.right.left) or
		(e.right = none and e = e.left.right)
}

-- All joints must be connected both left and right
fact {
	all j: Joint |
		j = j.left.right and 
		j = j.right.left and 
		j.left != j.right
}

-- All other vertices are reachable by following the right or left relation
fact {
	all v: Vertex |
		Vertex - v = v.(^left + ^right)
}


----------- Helper Function Section -----------

fun neighbors (v: Vertex): set Vertex {
	v.left + v.right
}

----------- Timestepping Section -----------

pred init (s: State) {
	all v: Vertex |
		s[v.carryLeft] = False and
		s[v.carryRight] = False
}

-- A vertex goes unchanged between states
pred stutter (v: Vertex, s, s': State) {
	all f: Vertex$.subfields |
		s[v.(f.value)] = s'[v.(f.value)]
}

-- All vertices in a set go unchanged between states
pred unchanged (vs: set Vertex, s, s': State) {
	all v: vs | stutter[v, s, s']
}

pred balance (v: Vertex, s, s': State) {
	s[v.momentLeft] != mo/first or s[v.momentRight] != mo/first
	s'[v.momentLeft] = mo/first
	s'[v.momentRight] = mo/first
	s'[v.carryLeft] = True
	s'[v.carryRight] = True
	unchanged[Vertex - v, s, s']
}

pred carleft (v: Vertex, s, s': State) {
	v.left != none
	s[v.carryLeft] = True
	s'[v.carryLeft] = False
	s'[v.carryRight] = s[v.carryRight]
	s'[(v.left).momentRight] = s[(v.left).momentRight].next
	s'[(v.left).momentRight] != none
}

pred carright (v: Vertex, s, s': State) {
	v.right != none
	s[v.carryRight] = True
	s'[v.carryRight] = False
	s'[v.carryLeft] = s[v.carryLeft]
	s'[(v.right).momentLeft] = s[(v.right).momentLeft].next
	s'[(v.right).momentLeft] != none
}

pred carboth (v: Vertex, s, s': State) {
	v.left != none and v.right != none
	s[v.carryRight] = True and s[v.carryLeft] = True
	s'[v.carryRight] = False and s[v.carryLeft] = False
	s'[(v.left).momentRight] = s[(v.left).momentRight].next
	s'[(v.right).momentLeft] = s[(v.right).momentLeft].next
	s'[(v.left).momentRight] != none
	s'[(v.right).momentLeft] != none
}

pred carryover (v: Vertex, s, s': State) {
	carleft[v, s, s'] or carright[v, s, s'] or carboth[v, s, s']
}

pred timestep(s, s': State) {
	-- Right now limit to one, but for parallel we'll change to any number
	one v: Vertex | balance[v, s, s'] or carryover[v, s, s']
--		stutter[v, s, s'] or
	--	balance[v, s, s']
}

----------- Running Stuff Section -----------

pred show {
	-- Leave out the case where there is no structure
	#Vertex = 3

	-- Initialize all vertices
	init[so/first]

	-- All but last step
	all s: State - so/last |
		timestep[s, s.next]
}
run show for 4
