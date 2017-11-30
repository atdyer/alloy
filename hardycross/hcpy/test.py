from Joint import FixedJoint, RollerJoint
from Span import Span
from Load import PointLoad, DistributedLoad
from Structure import Structure

A = FixedJoint('A')
B = RollerJoint('B')
C = RollerJoint('C')
D = RollerJoint('D')

AB = Span(7.5)
BC = Span(5)
CD = Span(6.25)

AB.add_load(PointLoad(10, 0.5))
BC.add_load(DistributedLoad(2))
CD.add_load(DistributedLoad(1.5))

S = Structure(A, AB, B, BC, C, CD, D)

S.solve(0.001)