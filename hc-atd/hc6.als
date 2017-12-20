module hc7

open util/boolean
open util/ordering[State] as so		-- state ordering

sig State {}
--sig Moment {}
abstract sig Vertex {
	left: lone Vertex,
	right: lone Vertex,
	zl: Bool one -> State,	-- left moment zeroed out
	zr: Bool one -> State,	-- right moment zeroed out
	cl: Bool one -> State,	-- has value to carry left
	cr: Bool one -> State		-- has value to carry right
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
		s[v.cl] = False and
		s[v.cr] = False and
		s[v.zl] = False and
		s[v.zr] = False
}

pred stutter (v: Vertex, s, s': State) {
	all f: Vertex$.subfields |
		s[v.(f.value)] = s'[v.(f.value)]
}

pred balance (v: Vertex, s, s': State) {
	s'[v.zl] = True
	s'[v.zr] = True
	v.left != none implies s'[v.cl] = True else s'[v.cl] = s[v.cl]
	v.right != none implies s'[v.cr] = True else s'[v.cr] = s[v.cr]
}

pred sendLeft (v: Vertex, s, s': State) {
	v.left != none
	s[v.cl] = True
	s'[v.cl] = False
	--s'[v.left.zr] = False
}

pred sendRight (v: Vertex, s, s': State) {
	v.right != none
	s[v.cr] = True
	s'[v.cr] = False
	--s'[v.right.zl] = False
}

pred send (v: Vertex, s, s': State) {
	s'[v.zl] = s[v.zl]
	s'[v.zr] = s[v.zr]
	(
		(sendLeft[v, s, s'] and s'[v.cr] = s[v.cr]) or
		(sendRight[v, s, s'] and s'[v.cl] = s[v.cl]) or
		(sendLeft[v, s, s'] and sendRight[v, s, s'])
	)
}

pred receiveFromLeft (v: Vertex, s, s': State) {
	v.left != none
	s[v.left.cr] = True
	s'[v.left.cr] = False
	--s'[v.zr] = False
}

pred receiveFromRight (v: Vertex, s, s': State) {
	v.right != none
	s[v.right.cl] = True
	s'[v.right.cl] = False
	--s'[v.zl] = False
}

pred receive (v: Vertex, s, s': State) {
	s'[v.cl] = s[v.cl]
	s'[v.cr] = s[v.cr]
	(
		(receiveFromLeft[v, s, s'] and s'[v.zr] = s[v.zr]) or
		(receiveFromRight[v, s, s'] and s'[v.zl] = s[v.zl]) or
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
		v.zl.last = True and
		v.zr.last = True and
		v.cl.last = False and
		v.cr.last = False

}

run show for 3
