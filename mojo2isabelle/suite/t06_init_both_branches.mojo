struct S:
    var x: Int

    def __init__(out self, c: Bool):
        if c:
            self.x = 1
        else:
            self.x = 2

def main():
    var s = S(False)
    print(s.x)
