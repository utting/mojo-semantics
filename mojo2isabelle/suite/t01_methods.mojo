struct Counter:
    var n: Int

    def __init__(out self):
        self.n = 0

    def inc(mut self):
        self.n += 1

    def get(self) -> Int:
        return self.n

def main():
    var c = Counter()
    c.inc()
    c.inc()
    print(c.get())
