@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def f(var a: Res, var b: Res):
    print("in f")
    print(b.id)
    print("after b")

def main():
    var x = Res(1)
    var y = Res(2)
    f(x^, y^)
    print("end")
