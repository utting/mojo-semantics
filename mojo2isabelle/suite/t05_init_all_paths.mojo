struct S:
    var x: Int

    def __init__(out self, c: Bool):
        if c:
            self.x = 1

def main():
    var s = S(True)
    print(s.x)
