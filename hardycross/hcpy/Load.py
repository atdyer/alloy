from abc import ABC, abstractmethod

class Load(ABC):

    def __init__(self):

        self._length = 1

    def set_span_length(self, length):

        self._length = length

    @abstractmethod
    def moment_left(self):
        pass

    @abstractmethod
    def moment_right(self):
        pass

class PointLoad(Load):

    def __init__(self, P, l):

        super().__init__()

        self._P = P
        self._l = l

    def __repr__(self):

        return 'PointLoad({}, {})'.format(self._P, self._l)

    def __str__(self):

        return 'Point Load: {} at {:.1%} of length of span'.format(self._P, self._l)

    def moment_left(self):
        a = self._l * self._length
        b = (1 - self._l) * self._length
        return -(self._P * a * b**2) / self._length**2

    def moment_right(self):
        a = self._l * self._length
        b = (1 - self._l) * self._length
        return (self._P * b * a**2) / self._length**2

class DistributedLoad(Load):

    def __init__(self, w):

        super().__init__()

        self._w = w

    def __repr__(self):

        return 'DistributedLoad({})'.format(self._w)

    def __str__(self):

        return 'Distributed Load: {}'.format(self._w)

    def moment_left(self):
        return -self._w * self._length**2 / 12

    def moment_right(self):
        return self._w * self._length**2 / 12