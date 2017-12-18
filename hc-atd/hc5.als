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

----------- Running Stuff Section -----------

pred show {
	-- Leave out the case where there is no structure
	#Vertex > 0

	-- Initialize all vertices
	init[so/first]
}
run show for 3
