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

    def solve(self):

        # Initialize
        for item in self._items:

            if isinstance(item, Joint):
                item.calculate_distribution_factors()
                item.calculate_fixed_end_moments()

            elif isinstance(item, Span):
                item.calculate_carryover_factors()

        self.print_distribution_factors()
        self.print_moments()

        # Iterate
        for i in range(10):
            for item in self._items:

                if isinstance(item, Joint):
                    item.balance(-item.moment())

            self.print_moments()

    def print_moments(self):

        string = ''

        for i, item in enumerate(self._items):

            if i % 2 == 0:

                if i == 0:

                    string += '{} {: .3f}{}'.format(
                        item,
                        item._moment_right,
                        ' '*5
                    )

                elif i == len(self._items) - 1:

                    string += '{: .3f} {}'.format(
                        item._moment_left,
                        item
                    )

                else:

                    string += '{: .3f} {} {: .3f}     '.format(
                        item._moment_left,
                        item,
                        item._moment_right
                    )

        print(string)

    def print_distribution_factors(self):

        string = ''

        for i, item in enumerate(self._items):

            if i % 2 == 0:

                if i == 0:

                    string += '{} {: .3f}{}'.format(
                        item,
                        item._distribution_factor_right,
                        ' ' * 5
                    )

                elif i == len(self._items) - 1:

                    string += '{: .3f} {}'.format(
                        item._distribution_factor_left,
                        item
                    )

                else:

                    string += '{: .3f} {} {: .3f}     '.format(
                        item._distribution_factor_left,
                        item,
                        item._distribution_factor_right
                    )

        print(string)
