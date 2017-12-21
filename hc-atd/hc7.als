module hc7

open util/boolean
open util/ordering[State] as so
open util/ordering[Moment] as mo

sig State {}
sig Moment {}
abstract sig Vertex {
	left: lone Vertex,
	right: lone Vertex,
	carryL: Bool one -> State,
	carryR: Bool one -> State,
	momentL: Moment one -> State,
	momentR: Moment one -> State
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

----------- Timestepping Section -----------

pred init (s: State) {
	all v: Vertex |
		s[v.carryL] = False and
		s[v.carryR] = False and
		s[v.momentL] != mo/first and
		s[v.momentR] != mo/first
}

pred stutter (v: Vertex, s, s': State) {
	all f: Vertex$.subfields |
		s[v.(f.value)] = s'[v.(f.value)]
}

pred balance (v: Vertex, s, s': State) {
	s'[v.momentL] = mo/first
	s'[v.momentR] = mo/first
	v.left != none implies s'[v.carryL] = True else s'[v.carryL] = s[v.carryL]
	v.right != none implies s'[v.carryR] = True else s'[v.carryR] = s[v.carryR]
}

pred sendLeft (v: Vertex, s, s': State) {
	v.left != none
	s[v.carryL] = True
	s'[v.carryL] = False
	-- COMMENT OUT TO ALLOW FOR CONVERGENCE
	--s'[v.left.momentR] = s[v.left.momentR].next
}

pred sendRight (v: Vertex, s, s': State) {
	v.right != none
	s[v.carryR] = True
	s'[v.carryR] = False
	-- COMMENT OUT TO ALLOW FOR CONVERGENCE
	--s'[v.right.momentL] = s[v.right.momentL].next
}

pred send (v: Vertex, s, s': State) {
	s'[v.momentL] = s[v.momentL]
	s'[v.momentR] = s[v.momentR]
	(
		(sendLeft[v, s, s'] and s'[v.carryR] = s[v.carryR]) or
		(sendRight[v, s, s'] and s'[v.carryL] = s[v.carryL]) or
		(sendLeft[v, s, s'] and sendRight[v, s, s'])
	)
}

pred receiveFromLeft (v: Vertex, s, s': State) {
	v.left != none
	s[v.left.carryR] = True
	s'[v.left.carryR] = False
	-- COMMENT OUT TO ALLOW FOR CONVERGENCE
	--s'[v.momentR] = s[v.momentR].next
}

pred receiveFromRight (v: Vertex, s, s': State) {
	v.right != none
	s[v.right.carryL] = True
	s'[v.right.carryL] = True
	-- COMMENT OUT TO ALLOW FOR CONVERGENCE
	--s'[v.momentL] = s[v.momentL].next
}

pred receive (v: Vertex, s, s': State) {
	s'[v.carryL] = s[v.carryL]
	s'[v.carryR] = s[v.carryR]
	(
		(receiveFromLeft[v, s, s'] and s'[v.momentR] = s[v.momentR]) or
		(receiveFromRight[v, s, s'] and s'[v.momentL] = s[v.momentL]) or
		(receiveFromLeft[v, s, s'] and receiveFromRight[v, s, s'])
	)
}

pred timestep (s, s': State) {
	
	all v: Vertex |
		stutter[v, s, s'] or
		balance[v, s, s'] or
		send[v, s, s'] or
		receive[v, s, s']

}

----------- Running Stuff Section -----------

pred show {
	
	#Vertex = 3

	init[so/first]
	
	all s: State - so/last |
		timestep[s, s.next]

	all v: Vertex |
		v.momentL.last = mo/first and
		v.momentR.last = mo/first and
		v.carryL.last = False and
		v.carryR.last = False

}

run show for 3
