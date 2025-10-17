import z3

class Mapper:
    def __init__(self, fa):
        self.Element = z3.DeclareSort('Element')
        self.start = self.element(0)
        self.map = z3.Function('map', self.Element, fa.State)
        self._elements = dict()

    def element(self, name):
        return z3.Const("n"+str(name), self.Element)