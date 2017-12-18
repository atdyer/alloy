
module hc4 -- version 0.04 (make member end moments the basic state variables)

/*
 * A model of the Hardy Cross method of moment distribution
 *
 * Date: December 16, 2017
 * Alloy Analyzer 4.2_2015-02-22 (build date: 2015-02-22 18:21 EST)
 *
 */

open util/graph [Vertex]
open util/ordering [State] as so
open util/ordering [Weight] as wo

abstract sig Vertex { e: set Vertex }

fact { noSelfLoops[e] and undirected[e] and stronglyConnected[e] }

-- the weight of member ends at a joint, a total order, represents the
-- degree of imalance of the joint ... if all its ends are min, the joint
-- is considered balanced
sig Weight {}

-- the state is just a weight associated with each edge
sig State { w: Vertex -> Vertex -> lone Weight }

fun edge [s: State]: Vertex -> Vertex {
  { x, y: Vertex | one s.w[x, y] }
}

-- the graph is (should be) unchanging, static ... it doesn't change
-- with any steps that are taken
fact { all s: State | edge[s] = e }

pred balanced [v: Vertex, s: State] {
  all x, y: Vertex | x->y in e => s.w[x, y] = wo/first
}

pred init [s: State] {
  let second = wo/first.wo/next |
    all x, y: Vertex | x->y in e => s.w[x, y] = second
}

pred step [s, s': State] {
--  unchanged[Joint, s, s'] or    -- allow stuttering?
  one v: Vertex | release[v, s, s']
}

pred release [v: Vertex, s, s': State] {
  not balanced[v, s]
  all x, y: Vertex |
    x->y in e => {
      v = x => distribute[x, y, s, s']
      v = y => carryover[x, y, s, s']
      v != x and v != y => unchanged[x, y, s, s']
    }
}

pred distribute [x, y: Vertex, s, s': State] {
  s'.w[x, y] = wo/first
}

-- carryover can leave a neighboring vertex balanced
pred carryover [x, y: Vertex, s, s': State] {
  lte[s'.w[x, y], s.w[x, y].wo/next]
}

pred unchanged [x, y: Vertex, s, s': State] {
  s'.w[x, y] = s.w[x, y]
}

one sig A, B, C extends Vertex {}

pred example {  -- from Baugh/Liu (except every joint can be released)
  A->B in e
  B->C in e
  A->C not in e
}

pred show {
  example
  init[so/first]  -- start with all unbalanced
  all s: State - so/last | step[s, s.so/next]
  all v: Vertex | balanced[v, so/last]  -- end with all balanced
}

run show for 4 but 4 Weight, 7 State
