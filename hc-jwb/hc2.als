
module hc2 -- version 0.02 (make all joints balance in the end)

/*
 * A model of the Hardy Cross method of moment distribution
 *
 * Date: December 10, 2017
 * Alloy Analyzer 4.2_2015-02-22 (build date: 2015-02-22 18:21 EST)
 *
 */

-- hardwired for the example from Baugh/Liu: need to define what
-- topologies are allowed to address arbitrary problems (yet to
-- be done)

-- might be interesting to show that a red/black ordering scheme
-- is a refinment of this (yet to be done)

-- each joint is a concurrent process: predicate abstraction is
-- used to determine whether moments balance at a joint

-- releasing a joint consists of 2 steps: distribute and carryover
--   1. distributing a moment at a joint causes the joint to balance
--   2. carrying over a moment to a neighbor joint causes the
--      neighbor joint to become unbalanced (in reality, as we near
--      convergence, a carryover moment may be so small that it may
--      leave a neighbor joint balanced)

-- note that we have abstracted away any "lost update" concern that
-- results from first reading and then distributing moments

open util/graph[Vertex]
open util/ordering [State]

abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig Vertex { e: set Vertex }

fact { noSelfLoops[e] and undirected[e] and stronglyConnected[e] }

sig State {}

abstract sig Counter {}
one sig c0, c1 extends Counter {}

sig Joint extends Vertex {
  pc: Counter one -> State,
  balanced: Bool one -> State
}

one sig A, B, C extends Joint {}

pred init [s: State] {
  all j: Joint | j.pc.s = c0 and j.balanced.s = False
}

pred distribute [j: Joint, s, s': State] {
  j.pc.s = c0 and j.balanced.s = False
  j.pc.s' = c1 and j.balanced.s' = True
  unchanged[Joint - j, s, s']
}

pred carryover [j: Joint, s, s': State] {
  j.pc.s = c1
  j.pc.s' = c0 and j.balanced.s' = j.balanced.s
  let neighbors = { k: Joint | j->k in e } {
    -- allow carryover to leave a neighbor balanced
    all n: neighbors {
      n.pc.s' = n.pc.s
      n.balanced.s = False implies n.balanced.s' = False
    }
    unchanged[Joint - j - neighbors, s, s']
  }
}

pred unchanged [js: set Joint, s, s': State] {
  all j: js | j.pc.s' = j.pc.s and j.balanced.s' = j.balanced.s
}

pred step [s, s': State] {
--  unchanged[Joint, s, s'] or    -- allow stuttering?
  one j: Joint | distribute[j, s, s'] or carryover[j, s, s']
}

pred example {  -- from Baugh/Liu (except every joint can be released)
  #Joint = 3
  A->B in e
  B->C in e
  A->C not in e
}

pred show {
  example
  init[first]
  all s: State - last | step[s, s.next]
--  all balanced and all carryover moments applied:
  all j: Joint | j.pc.last = c0 and j.balanced.last = True
--  (works if we allow carryover moments to leave a joint balanced,
--  but only when we run for n States where n = 11, 17, 23, ...
--  unless we allow stuttering, which adds flexibility)
}

run show for 10 but 3 Int, 11 State

-- max integer for "n Int" = 2^(n-1) - 1
--    n = 10, max = 511
--    n =  8, max = 127
--    n =  6, max = 31
--    n =  5, max = 15


