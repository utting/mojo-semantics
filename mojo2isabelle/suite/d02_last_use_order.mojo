@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var a = Res(1)
    var b = Res(2)
    print(b.id)
    print(a.id)
    print("end")
