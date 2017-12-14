module converge

open util/graph[Step]

abstract sig Step {
	num: Int
}
sig Converged extends Step {}
sig Iteration extends Step {
	next: Step
}

fact {
	#Converged = 1
	tree[next]
	Converged.num = 0
	all i: Iteration | i.num = i.next.num.add[1]
}

pred show {}
run show for 7
