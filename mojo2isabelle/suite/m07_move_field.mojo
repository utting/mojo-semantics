@fieldwise_init
struct Pair:
    var x: Res
    var y: Res

@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def eat(var r: Res):
    print("eat", r.id)

def main():
    var p = Pair(Res(1), Res(2))
    eat(p.x^)
    print(p.y.id)
