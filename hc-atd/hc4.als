module hc4	-- version 0.04

-- New way of describing connectivity that will allow
-- for a finer grained approach to moment distrubution

abstract sig Vertex {
	left: lone Vertex,
	right: lone Vertex
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

----------- Running Stuff Section -----------

pred show {
	#Vertex > 0
}
run show for 5
