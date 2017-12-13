module hc2	-- version 0.02

open util/boolean
open util/graph[Joint]
open util/ordering[State]

----------- Signatures Section -----------
-- A Vertex is abstract, and can be either a Joint or an End
-- Structures describe connectivity of Vertices through spans

sig State {}
abstract sig Vertex {
	balanced: Bool one -> State,	-- Indicates if left/right moments balance out to ~zero
	carryable: Bool one -> State	-- Indicates if a moment value needs to be carried over
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
	all s: Structure | all e: End | s.span[e] in Vertex and #s.span[e] = 1
}

-- Ends are reachable from each other (not needed, but fun nonetheless)
fact {
	all s: Structure | all e: End | e -> (End-e) in ^(s.span)
}

----------- Helper Function Section -----------

fun neighbors (v: Vertex): set Vertex {
	Structure.span[v]
}

----------- Timestepping Section -----------

-- Initialize all vertices to be unbalanced
pred init (s: State) {
	all v: Vertex | 
		v.balanced.s = False and
		v.carryable.s = False
}

-- All vertices in the set are identical between the two states
pred unchanged (vs: set Vertex, s, s': State) {
	all v: vs | 
		s[v.balanced] = s'[v.balanced] and
		s[v.carryable] = s'[v.carryable]
}

-- Balance a single vertex
pred balance (v: Vertex, s, s': State) {
	s[v.balanced]   = False
	s[v.carryable]  = False
	s'[v.balanced]  = True
	s'[v.carryable] = True
	unchanged[Vertex - v, s, s']
}

-- Carryover values, causing neighboring vertices to
-- either become unbalanced or stutter (i.e carryover
-- contribution doesn't put moment value outside
-- desired level of precision)
pred carryover (v: Vertex, s, s': State) {
	s[v.balanced] = s'[v.balanced]
	s[v.carryable] = True
	s'[v.carryable] = False
	all n: neighbors[v] {
		s[n.carryable] = s'[n.carryable]
		-- Of note:
		--   This statement allows the case in which carryover does
		--   not cause a neighboring vertex to become unbalanced.
		--   In in implementation, this occurs when the solution
		--   has converged.
		s[n.balanced] = False implies s'[n.balanced] = False
		--   This statement, which requires that carryover always
		--   makes a neighboring vertex become unbalanced, will
		--   never produce a viable instance
		-- s'[n.balanced] = False
	}
	unchanged[Vertex - v - neighbors[v], s, s']
}

-- Advance a single timestep, changing state by either
-- balancing or carrying over
pred timestep (s, s': State) {
	one v: Vertex | 
		balance[v, s, s'] or 
		carryover[v, s, s']
}

----------- Running Stuff Section -----------

pred show {
	-- Initialize all vertices as not balanced
	init[first]

	-- In each intermediate timestep,  
	all s: State - last | 
		timestep[s, s.next]

	-- The final timestep must have all vertices balanced
	-- with no values left to carry over
	all v: Vertex | 
		v.balanced.last = True and 
		v.carryable.last = False
}

-- Minimum n=7 to find instance
run show for 7

-- Interesting case where vertex becomes unbalanced
-- and still needs to carry over
-- run show for 11 but 3 Vertex
