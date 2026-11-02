@fieldwise_init
struct P:
    var x: Int

def main():
    var p = P(1)
    ref r = p.x
    p.x = 4
    print(r)
