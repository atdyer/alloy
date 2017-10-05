module mesh

--sig Mesh {
--	triangles: some Triangle,
--	adj: Triangle -> Triangle
--}

--sig Triangle {
--	edges: Vertex -> Vertex
--}

sig Vertex {}

-- every triangle appears in a mesh
fact { all t: Triangle | t in Mesh.triangles }

pred show {}
run show for 2 but 2 Vertex
