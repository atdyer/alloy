from LinkedList import DLLItem
from Joint import FixedJoint, RollerJoint

class Span(DLLItem):

    def __init__(self, length):

        super().__init__()

        self._E = 1
        self._I = 1
        self._length = length
        self._COF_left = 0.5
        self._COF_right = 0.5
        self._loads = []

    def __repr__(self):

        return 'Span()'

    def __str__(self):

        return '{}{}'.format(self.left(), self.right())

    def E(self, *E):

        if len(E) > 0:
            self._E = E[0]
            return self
        return self._E

    def add_load(self, load):

        load.set_span_length(self._length)
        self._loads.append(load)

    def calculate_carryover_factors(self):

        if self.left() is None or self.right() is None:

            raise AttributeError('Structure has not been correctly defined')

        if isinstance(self.left(), RollerJoint) and isinstance(self.right(), FixedJoint):

            self._COF_left = 0
            self._COF_right = 0.5

        if isinstance(self.right(), RollerJoint) and isinstance(self.left(), FixedJoint):

            self._COF_left = 0.5
            self._COF_right = 0

    def carry_left(self, moment):

        if self.left() is not None:

            self.left().receive_from_right(self._COF_left * moment)

    def carry_right(self, moment):

        if self.right() is not None:

            self.right().receive_from_left(self._COF_right * moment)

    def length(self, *length):

        if len(length) > 0:

            if length[0] == 0:
                raise ValueError('Cannot set length to zero')
            self._length = length[0]
            for load in self._loads:
                load.set_span_length(self._length)
            return self
        return self._length

    def loads(self):

        for load in self._loads:
            yield load

    def EIL(self):

        return self._E * self._I / self._length