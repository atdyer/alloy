from Joint import FixedJoint, RollerJoint
from Span import Span
from Load import PointLoad, DistributedLoad
from Structure import Structure

#
#  From the wikipedia page on moment distribution method
#

A = RollerJoint('A')
B = RollerJoint('B')
C = RollerJoint('C')
D = FixedJoint('D')

AB = Span(10).E(1)
BC = Span(10).E(2)
CD = Span(10).E(1)

AB.add_load(PointLoad(10, 0.3))
BC.add_load(DistributedLoad(1))
CD.add_load(PointLoad(10, 0.5))

S = Structure(A, AB, B, BC, C, CD, D)

S.solve(0.0001)