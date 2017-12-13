
module hc3 -- version 0.03 (refinement ... but ignore carryover)

/*
 * A model of the Hardy Cross method of moment distribution
 *
 * Date: December 13, 2017
 * Alloy Analyzer 4.2_2015-02-22 (build date: 2015-02-22 18:21 EST)
 *
 */

open util/graph[Vertex]
open util/ordering [AS] as ao   -- abstract
open util/ordering [CS] as co   -- concrete

abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig Vertex { e: set Vertex }

fact { noSelfLoops[e] and undirected[e] and stronglyConnected[e] }

abstract sig State {}
sig AS, CS extends State {}

sig Joint extends Vertex {
  balanced: Bool one -> State
}

one sig A, B, C extends Joint {}

pred init [s: State] {
  all j: Joint | j.balanced.s = False
}

pred distribute [j: Joint, s, s': State] {
  j.balanced.s = False
  j.balanced.s' = True
  unchanged[Joint - j, s, s']
}

pred unchanged [js: set Joint, s, s': State] {
  all j: js | j.balanced.s' = j.balanced.s
}

pred step [s, s': State] {
  unchanged[Joint, s, s'] or    -- allow stuttering?
  one j: Joint | distribute[j, s, s']
}

pred example {  -- from Baugh/Liu (except every joint can be released)
  #Joint = 3
  A->B in e
  B->C in e
  A->C not in e
}

pred abstr {
  init[ao/first]
  all s: AS - ao/last | step[s, s.ao/next]
  all j: Joint | j.balanced.ao/last = True
}

pred concr {
  init[co/first]
  all s: CS - co/last | step[s, s.co/next]
  all j: Joint | j.balanced.co/last = True
}

pred show {
  example
  abstr
  concr  
}

run show for 10 but 3 Int, 8 State, 4 AS, 4 CS

-- max integer for "n Int" = 2^(n-1) - 1
--    n = 10, max = 511
--    n =  8, max = 127
--    n =  6, max = 31
--    n =  5, max = 15
