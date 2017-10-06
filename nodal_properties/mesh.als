module mesh

open util/relation								-- dom, ran, symmetric, irreflexive

sig Mesh {
	triangles: some Triangle,
	adj: Triangle -> Triangle
}

sig Triangle {
	edges: Vertex -> Vertex
}

sig Vertex {}

-- every triangle appears in a mesh
fact { all t: Triangle | t in Mesh.triangles }

-- every vertex appears in some triangle
fact { all v: Vertex | v in dom[Mesh.triangles.edges] }

-- every triangle has exactly 3 edges
fact { all t: Triangle | #t.edges = 3 }


fact { all t: Triangle | ring[t.edges] }

-- the edge set e forms a ring
pred ring [e: Vertex->Vertex] {
	all v: dom[e] | one v.e and dom[e] in v.^e
}

pred show {}
run show for 3 but exactly 2 Mesh
