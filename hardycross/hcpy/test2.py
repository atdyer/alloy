from Joint import FixedJoint, RollerJoint
from Span import Span
from Load import PointLoad, DistributedLoad
from Structure import Structure

#
# Example from Baugh, Liu paper
#

A = FixedJoint('A')
B = RollerJoint('B')
C = RollerJoint('C')

AB = Span(10)
BC = Span(10)

AB.add_load(PointLoad(120, 0.4))
BC.add_load(DistributedLoad(50))

S = Structure(A, AB, B, BC, C)

S.solve(0.0001)