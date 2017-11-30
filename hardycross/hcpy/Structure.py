from Joint import Joint
from Span import Span

class Structure:

    def __init__(self, *items):

        self._items = items
        n = len(items)

        if n > 0:

            if not isinstance(items[0], Joint) or not isinstance(items[n-1], Joint):

                raise ValueError('Structure must begin and end with a joint')

            for i in range(n-1):

                items[i].right(items[i+1])

            for i in reversed(range(1, n)):

                items[i].left(items[i-1])

            for i in range(n):

                if ((i % 2 == 0 and not isinstance(items[i], Joint)) or
                        (i % 2 == 1 and not isinstance(items[i], Span))):

                    raise ValueError('Joints and spans must alternate')

            self._left = items[0]

        else:

            self._left = None

    def __repr__(self):

        return 'Structure{}'.format(self._items)

    def __str__(self):

        if self._left:

            return self._left.to_string()

        return 'Undefined structure'

    def solve(self, tolerance, print_table=True):

        joints = [joint for joint in self._items if isinstance(joint, Joint)]
        spans = [span for span in self._items if isinstance(span, Span)]

        # Initialize
        for item in self._items:

            if isinstance(item, Joint):
                item.calculate_distribution_factors()
                item.calculate_fixed_end_moments()

            elif isinstance(item, Span):
                item.calculate_carryover_factors()

        i = 0

        # Iterate
        while abs(sum(map(Joint.moment, joints))) > tolerance:

            i += 1

            if print_table:
                self.print_moments()

            for joint in joints:
                joint.balance()

            if print_table:
                self.print_balance()

            for span in spans:
                span.carryover()

            if print_table:
                self.print_carryovers()

            for joint in joints:
                joint.sum()

        print()
        print('Iterations: {}\tTolerance: {}'.format(i, tolerance))
        self.print_moments()

    def print_moments(self):

        self.print_row('Moments', Joint, Joint.moment_left, Joint.moment_right)

    def print_balance(self):

        self.print_row('Balance', Joint, Joint.balance_left, Joint.balance_right)

    def print_carryovers(self):

        self.print_row('CO', Joint, Joint.carryover_left, Joint.carryover_right)

    def print_row(self, name, T, method_left, method_right):

        string = '{}\t\t'.format(name)
        spacing = 5

        for i, item in enumerate(self._items):

            if isinstance(item, T):

                if i == 0:

                    string += '{} {: 8.3f} {}'.format(
                        item,
                        method_right(item),
                        ' '*spacing
                    )

                elif i == len(self._items) - 1:

                    string += '{: 8.3f} {}'.format(
                        method_left(item),
                        item
                    )

                else:

                    string += '{: 8.3f} {} {: 8.3f} {}'.format(
                        method_left(item),
                        item,
                        method_right(item),
                        ' '*spacing
                    )

        print(string)
