from random import sample, randint

class End(object):

	def __init__(self, d, c, m):
		self.d, self.c, self.m = d, c, m
	
	def __repr__(self):
		return repr([self.d, self.c, self.m])

class Vertex(object):
	
	def __init__(self, name):
		self.name = name
	
	def __repr__(self):
		return repr(self.name)

def model_problem():
	a, b, c = Vertex('a'), Vertex('b'), Vertex('c')
	G = {a: {}, b: {}, c: {}}
	G[a][b] = End(0.0, 0.5, -172.8)
	G[b][a] = End(0.5, 0.5, 115.2)
	G[b][c] = End(0.5, 0.5, -416.7)
	G[c][b] = End(1.0, 0.5, 416.7)
	return G

def ends(G, u):
	return G[u].values()

def moment(G, u):
	return sum([e.m for e in ends(G, u)])

def active(G):
	return {u: G[u] for u in G if any(e.d > 0 for e in ends(G, u))}
	
def release(G, u, x):
	for v in G[u]:
		G[u][v].m -= G[u][v].d * x
		G[v][u].m -= G[u][v].c * G[u][v].d * x

def solve_con(G, tol):
	converged = False
	while not converged:
		converged = True
		for v in active(G):
			if abs(moment(G, v)) > tol:
				converged = False
				release(G, v, moment(G, v))

def solve_sim(G, tol):
	converged = False
	while not converged:
		converged = True
		for v in active(G):
			v.m = moment(G, v)
		for v in active(G):
			if abs(v.m) > tol:
				converged = False
				release(G, v, v.m)
				
def subset(G):
	return sample(G.keys(), randint(0, len(G)))

def solve_seq(G, tol):
	converged = False
	while not converged:
		converged = True
		s = subset(active(G))
		for v in active(G):
			v.m = moment(G, v)
		for v in active(G):
			if abs(v.m) > tol:
				converged = False
				if v in s:
					release(G, v, v.m)

def moments(G):
	return {u.name + v.name: G[u][v].m for u in G for v in G[u]}

def main():
	for solve in [solve_sim, solve_con, solve_seq]:
		G = model_problem()
		solve(G, 0.001)
		print(moments(G))

if __name__ == '__main__':
	main()
