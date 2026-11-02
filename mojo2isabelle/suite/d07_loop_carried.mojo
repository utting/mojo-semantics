@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var keep = Res(0)
    var i = 1
    while i <= 2:
        var r = Res(i)
        print("iter", r.id, keep.id)
        i += 1
    print("done")
