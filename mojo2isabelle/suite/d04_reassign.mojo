@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var a = Res(1)
    a = Res(2)
    print("mid", a.id)
    a = Res(3)
    print("end")
