@fieldwise_init
struct C:
    var n: Int

def inc(mut c: C):
    c.n += 1

def twice(mut c: C):
    inc(c)
    inc(c)

def main():
    var c = C(0)
    twice(c)
    print(c.n)
