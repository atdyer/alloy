from abc import ABC, abstractmethod
from LinkedList import DLLItem

class Joint(DLLItem, ABC):

    def __init__(self, name):

        super().__init__()

        self._name = name
        self._distribution_factor_left = None
        self._distribution_factor_right = None
        self._moment_left = None
        self._moment_right = None
        self._balance_left = 0
        self._balance_right = 0
        self._CO_left = 0
        self._CO_right = 0

    def __str__(self):

        return '{}'.format(self._name)

    def balance(self):

        moment = -self.moment()
        self._balance_left = self._distribution_factor_left * moment
        self._balance_right = self._distribution_factor_right * moment

    def sum(self):

        self._moment_left += self._balance_left + self._CO_left
        self._moment_right += self._balance_right + self._CO_right

    def balance_left(self):

        return self._balance_left

    def balance_right(self):

        return self._balance_right

    def carryover_left(self, *CO):

        if len(CO) > 0:
            self._CO_left = CO[0]
            return self
        return self._CO_left

    def carryover_right(self, *CO):

        if len(CO) > 0:
            self._CO_right = CO[0]
            return self
        return self._CO_right

    def moment(self):

        return self._moment_right + self._moment_left

    def moment_left(self):

        return self._moment_left

    def moment_right(self):

        return self._moment_right

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

        return self

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

        return self

    def calculate_fixed_end_moments(self):

        super().calculate_fixed_end_moments()

        if self.left() is None:
            self._moment_left = -self._moment_right

        if self.right() is None:
            self._moment_right = -self._moment_left

        return self

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

        return self