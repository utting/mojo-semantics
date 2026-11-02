@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var a = Res(1)
    print("x")
    var b = Res(2)
    print("y")
