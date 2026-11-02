@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def make(n: Int) -> Res:
    return Res(n)

def main():
    make(7)
    print("after")
    var r = make(8)
    print("end")
