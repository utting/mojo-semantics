@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var a = Res(1)
    var b = a^
    print("b", b.id)
    print("end")
