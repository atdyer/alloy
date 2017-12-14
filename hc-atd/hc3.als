module hc3	-- version 0.03

open util/boolean
open util/graph[Vertex]
open util/ordering[State]

----------- Signatures Section -----------
-- A Vertex is abstract, and can be either a Joint or an End
-- Structures describe connectivity of Vertices through spans

sig State {}
abstract sig Vertex {
	balanced: Bool one -> State,	-- Indicates if left/right moments balance out to ~zero
	carryable: Bool one -> State,	-- Indicates if a moment value needs to be carried over
	remaining: Int one -> State		-- The number of remaining iterations before convergence
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

----------- Iterations and Convergence -----------

-- All vertices will take some number of (or no) iterations to converge
fact {
	all s: State | all v: Vertex | gte[s[v.remaining], 0]
	--all v: Vertex | gt[v<:remaining, 0]
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
		s[v.carryable] = s'[v.carryable] and
		unchangedIterations[vs, s, s']
}

pred unchangedIterations (vs: set Vertex, s, s': State) {
	all v: vs |
		eq[s[v.remaining], s'[v.remaining]]
}

-- Balance a single vertex
pred balance (v: Vertex, s, s': State) {
	s[v.balanced]   = False
	s[v.carryable]  = False
	s'[v.balanced]  = True
	s'[v.carryable] = True
	eq[s'[v.remaining], sub[s[v.remaining], 1]]
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
		-- s[n.balanced] = False implies s'[n.balanced] = False
		--   This statement, which requires that carryover always
		--   makes a neighboring vertex become unbalanced, will
		--   never produce a viable instance
		-- s'[n.balanced] = False
		--   This statement is meant to represent a more concrete
		--   example of convergence. If the neighboring vertex is
		--   balanced but still has remaining iterations, the carryover
		--   will cause it to become unbalanced.
		s[n.balanced] = True and gt[s[n.remaining], 0] implies s'[n.balanced] = False
	}
	unchanged[Vertex - v - neighbors[v], s, s']
	unchangedIterations[Vertex, s, s']
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
		v.carryable.last = False and
		eq[v.remaining.last, 0]
}

-- Minimum n=3 to find instance
run show for 3

