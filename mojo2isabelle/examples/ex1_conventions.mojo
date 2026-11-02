@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def consume(var r: Res):
    print("got", r.id)

def bump(mut r: Res, n: Int):
    r.id += n

def pick(c: Bool, ref a: Res, ref b: Res) -> ref[a, b] Res:
    if c:
        return a
    else:
        return b

def main():
    var a = Res(1)
    var b = Res(2)
    bump(a, 10)
    ref r = pick(True, a, b)
    print(r.id)                  # 11
    consume(a^)                  # got 11 / drop 11
    var l: List[Int] = [1, 2, 3]
    ref e = l[0]
    print(e)                     # 1
    l.append(4)
