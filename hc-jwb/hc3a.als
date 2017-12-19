
module hc3a -- version 0.03 (refinement ... but ignore carryover)

-- use just one total order for state, and create separate predicates
-- for abstract and concrete

/*
 * A model of the Hardy Cross method of moment distribution
 *
 * Date: December 19, 2017
 * Alloy Analyzer 4.2_2015-02-22 (build date: 2015-02-22 18:21 EST)
 *
 */

open util/graph [Vertex]
open util/ordering [Joint] as jo  -- to distribute in a fixed order
open util/ordering [State] as so

abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig Vertex { e: set Vertex }

fact { noSelfLoops[e] and undirected[e] and stronglyConnected[e] }

sig State {}

sig Joint extends Vertex {
  balanced: Bool one -> State
}

one sig A, B, C extends Joint {}

-- abstr: make some joints unbalanced to begin with
pred init_A [s: State] {
  some j: Joint | j.balanced.s = False
}

-- concr: make all joints unbalanced to begin with
pred init_C [s: State] {
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

-- abstr: distribute joints in any order
pred step_A [s, s': State] {
  unchanged[Joint, s, s'] or    -- allow stuttering?
  one j: Joint | distribute[j, s, s']
}

-- concr: distribute joint in ascending order
pred step_C [s, s': State] {
  unchanged[Joint, s, s'] or    -- allow stuttering?
  let j = min[{ k : Joint | k.balanced.s = False}] |
    distribute[j, s, s']
}

fact example {  -- from Baugh/Liu (except every joint can be released)
  -- #Joint = 3  <- force to be exactly 3 via scope declaration
  -- so that A, B, and C appear in lexicographic order:
  A = jo/first and B = A.jo/next and C = B.jo/next
  A->B in e
  B->C in e
  A->C not in e
}

pred abstr {
  init_A[so/first]
  all s: State - so/last | step_A[s, s.so/next]
  all j: Joint | j.balanced.so/last = True
}

run abstr for 10 but 3 Int, 3 Joint, 6 State

pred concr {
  init_C[so/first]
  all s: State - so/last | step_C[s, s.so/next]
  all j: Joint | j.balanced.so/last = True
}

run concr for 10 but 3 Int, 3 Joint, 6 State

assert refines {
  init_C[so/first] implies init_A[so/first]
  all s, s': State | step_C[s, s'] implies step_A[s, s']
}

check refines for 10 but 3 Int, 3 Joint, 6 State

-- max integer for "n Int" = 2^(n-1) - 1
--    n = 10, max = 511
--    n =  8, max = 127
--    n =  6, max = 31
--    n =  5, max = 15
