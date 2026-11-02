@fieldwise_init
struct P:
    var x: Int
    var y: Int

def swap(mut a: Int, mut b: Int):
    var t = a
    a = b
    b = t

def main():
    var p = P(1, 2)
    swap(p.x, p.y)
    print(p.x, p.y)
