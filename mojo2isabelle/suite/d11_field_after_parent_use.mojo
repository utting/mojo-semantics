@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

@fieldwise_init
struct Pair:
    var x: Res
    var y: Res

def main():
    var p = Pair(Res(1), Res(2))
    print(p.x.id)
    print("mid")
    print(p.y.id)
    print("end")
