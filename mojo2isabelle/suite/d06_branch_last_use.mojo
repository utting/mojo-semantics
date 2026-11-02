@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var a = Res(1)
    var b = Res(2)
    var c = True
    if c:
        print(a.id)
        print(b.id)
    else:
        print(b.id)
    print("end")
