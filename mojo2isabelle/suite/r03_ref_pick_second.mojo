@fieldwise_init
struct P:
    var x: Int

def pick(c: Bool, ref a: P, ref b: P) -> ref[a, b] P:
    if c:
        return a
    return b

def main():
    var a = P(1)
    var b = P(2)
    ref r = pick(False, a, b)
    r.x = 20
    print(a.x, b.x)
