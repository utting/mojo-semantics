@fieldwise_init
struct P(Copyable):
    var x: Int

def main():
    var a = P(1)
    var b = a
    b.x = 5
    print(a.x, b.x)
