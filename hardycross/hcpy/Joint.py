from abc import ABC, abstractmethod
from LinkedList import DLLItem

class Joint(DLLItem, ABC):

    def __init__(self, name):

        super().__init__()

        self._name = name
        self._moment_left = None
        self._moment_right = None
        self._distribution_factor_left = None
        self._distribution_factor_right = None

    def __str__(self):

        return '{}'.format(self._name)

    def balance(self, moment):

        left = self._distribution_factor_left * moment
        right = self._distribution_factor_right * moment

        self._moment_left += left
        self._moment_right += right

        if self.left() is not None:
            self.left().carry_left(left)

        if self.right() is not None:
            self.right().carry_right(right)

    def receive_from_right(self, moment):

        self._moment_right += moment

    def receive_from_left(self, moment):

        self._moment_left += moment

    def moment(self):

        return self._moment_right + self._moment_left

    def name(self):

        return self._name

    def calculate_fixed_end_moments(self):

        self._moment_left = 0
        self._moment_right = 0

        if self.left() is not None:

            for load in self.left().loads():

                self._moment_left += load.moment_right()

        if self.right() is not None:

            for load in self.right().loads():

                self._moment_right += load.moment_left()

    @abstractmethod
    def calculate_distribution_factors(self):
        pass

class FixedJoint(Joint):

    def __init__(self, name):

        super().__init__(name)

    def __repr__(self):

        return 'FixedJoint({})'.format(self._name)

    def calculate_distribution_factors(self):

        if self.left() is not None:
            self._distribution_factor_left = 0
        else:
            self._distribution_factor_left = 1

        if self.right() is not None:
            self._distribution_factor_right = 0
        else:
            self._distribution_factor_right = 1

    def calculate_fixed_end_moments(self):

        super().calculate_fixed_end_moments()

        if self.left() is None:
            self._moment_left = -self._moment_right

        if self.right() is None:
            self._moment_right = -self._moment_left

class RollerJoint(Joint):

    def __init__(self, name):

        super().__init__(name)

    def __repr__(self):

        return 'RollerJoint({})'.format(self._name)

    def calculate_distribution_factors(self):

        if self.left() is None:
            self._distribution_factor_left = 0
        else:
            left = self.left().EIL()
            right = self.right().EIL() if self.right() is not None else 0
            self._distribution_factor_left = left / (left + right)

        if self.right() is None:
            self._distribution_factor_right = 0
        else:
            right = self.right().EIL()
            left = self.left().EIL() if self.left() is not None else 0
            self._distribution_factor_right = right / (left + right)