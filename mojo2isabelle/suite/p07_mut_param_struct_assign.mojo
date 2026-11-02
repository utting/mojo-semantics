@fieldwise_init
struct C:
    var n: Int

def reset(mut c: C):
    c = C(0)

def main():
    var c = C(5)
    reset(c)
    print(c.n)
