@fieldwise_init
struct Inner:
    var n: Int

    def inc(mut self):
        self.n += 1

@fieldwise_init
struct Outer:
    var i: Inner

def main():
    var o = Outer(Inner(1))
    o.i.inc()
    o.i.inc()
    print(o.i.n)
