@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def make2() -> Res:
    var a = Res(1)
    var b = Res(2)
    return b^

def main():
    var r = make2()
    print("got", r.id)
