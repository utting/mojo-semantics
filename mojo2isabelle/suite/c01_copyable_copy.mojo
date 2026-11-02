@fieldwise_init
struct P(Copyable):
    var x: Int
    var y: Int

def main():
    var a = P(1, 2)
    var b = a.copy()
    b.x = 10
    print(a.x, a.y, b.x, b.y)
