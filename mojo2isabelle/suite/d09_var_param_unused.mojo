@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def ignore(var r: Res):
    print("in ignore")

def main():
    var a = Res(1)
    ignore(a^)
    print("end")
