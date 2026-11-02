@fieldwise_init
struct C:
    var n: Int

def bump(var c: C) -> C:
    c.n += 1
    return c^

def main():
    var c = bump(C(1))
    print(c.n)
