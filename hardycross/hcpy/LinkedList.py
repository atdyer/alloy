
# An item in a doubly-linked-list
class DLLItem(object):

    def __init__(self):

        self._left = None
        self._right = None

    def left(self, *left):

        if len(left) > 0:
            self._left = left[0]
            return self
        return self._left

    def right(self, *right):

        if len(right) > 0:
            self._right = right[0]
            return self
        return self._right

    def to_string(self):

        if self._left:
            self._left.print()
        else:
            string = ''
            current = self
            while current:
                string += str(current) + ' '
                current = current.right()
            return string