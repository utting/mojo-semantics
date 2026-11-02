@fieldwise_init
struct P:
    var x: Int
    var y: Int

def main():
    var p = P(1, 2)
    ref r = p.x
    r = 5
    p.y += 1
    print(r, p.x, p.y)
