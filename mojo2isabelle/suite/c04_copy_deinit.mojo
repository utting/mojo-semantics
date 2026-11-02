@fieldwise_init
struct R(Copyable):
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var a = R(1)
    var b = a.copy()
    b.id = 2
    print("end")
