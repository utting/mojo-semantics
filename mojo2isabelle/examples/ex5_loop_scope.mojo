@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var i = 0
    while i < 3:
        var r = Res(i)
        i += 1
    print("done")       # drop 0 / drop 1 / drop 2 / done
