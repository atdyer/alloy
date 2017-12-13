module hc		-- version 0.01

open util/boolean
open util/graph[Joint]
open util/ordering[State]

----------- Signatures Section -----------
-- A Vertex is abstract, and can be either a Joint or an End
-- Structures describe connectivity of Vertices through spans

sig State {}
abstract sig Vertex {
	balanced: Bool one -> State
}
sig Joint extends Vertex {}
sig End extends Vertex {}
sig Structure {
	span: Vertex->Vertex
}


----------- Connectivity Section -----------

-- Define connectivity of spans
fact {
	noSelfLoops[Structure.span] and
	undirected[Structure.span] and
	stronglyConnected[Structure.span]
}

-- There must only be one structure with two ends and at least one joint
fact {
	#Structure = 1
	#End = 2
	#Joint >= 1
}

-- Joints must be connected to exactly two other vertices
fact {
	all s: Structure | all j: Joint | #s.span[j] = 2
}

-- Ends must be connected to one and only one Joint
fact {
	all s: Structure | all e: End | s.span[e] in Joint and #s.span[e] = 1
}

-- Ends are reachable from each other (not needed, but fun nonetheless)
fact {
	--all s: Structure | all e: End | e -> (End-e) in ^(s.span)
}


----------- Timestepping Section -----------

-- Initialize all vertices to be unbalanced
pred init (s: State) {
	all v: Vertex | v.balanced.s = False
}

-- All vertices in the set are identical between the two states
pred unchanged (vs: set Vertex, s, s': State) {
	all v: vs | s[v.balanced] = s'[v.balanced]
}

-- Balance a single vertex
pred balance (v: Vertex, s, s': State) {
	s[v.balanced] = False
	s'[v.balanced] = True
	unchanged[Vertex - v, s, s']
}

-- Advance a single timestep, changing state in one of
-- any possible way
pred timestep (s, s': State) {
	one v: Vertex | balance[v, s, s']
}

----------- Running Stuff Section -----------

pred show {
	-- Initialize all vertices as not balanced
	init[first]

	-- In each intermediate steps, only one vertex can become balanced 
	all s: State - last | timestep[s, s.next]

	-- The final timestep must have all vertices balanced
	all v: Vertex | v.balanced.last = True
}

-- # of Joints = n - 3
-- # solutions = (n-1) * (n-2)!
-- n = 4, E-J-E, 6
-- n = 5, E-J-J-E, 24
-- n = 6, E-J-J-J-E, 120
-- n = 7, E-J-J-J-J-E, 720
run show for 6
