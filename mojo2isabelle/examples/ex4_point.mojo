struct Point:
    var x: Int
    var y: Int

    def __init__(out self, a: Int):
        self.x = a
        self.y = a * 2

    def sum(self) -> Int:
        return self.x + self.y

    def scale(mut self, k: Int):
        self.x = self.x * k
        self.y = self.y * k

def make(n: Int) -> Point:
    var p = Point(n)
    return p^

def main():
    var p = make(3)
    p.scale(2)
    print(p.x, p.y, p.sum())    # 6 12 18
