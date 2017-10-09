module parallel

open mesh
open util/relation
open util/ordering [State] as so

abstract sig Bool {}
one sig True, False extends Bool {}

sig State {}

sig Node extends Vertex {
	valueWritten: Bool one -> State,
	valueCopied: Bool one -> State
}

sig Element extends Triangle {}

-- Make all vertices nodes and all triangles elements
fact { all v: Vertex | v in Node }
fact { all t: Triangle | t in Element }

-- Initialize all values as neither written nor copied
pred init [m: Mesh, s: State] {
	all n: m.nodes | n.valueWritten.s = False
	all n: m.nodes | n.valueCopied.s = False
}

-- The set of all nodes in a mesh
fun nodes [m: Mesh]: set Node { dom[m.triangles.edges] }

pred show [m: Mesh, s: Int -> State] {
	init[m, s[0]]
	#Mesh = 1
	#Triangle = 3
}

run show for 6 but 8 int
