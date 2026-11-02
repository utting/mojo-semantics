@fieldwise_init
struct Acc:
    var total: Int
    var n: Int
    def __deinit__(deinit self):
        print("acc", self.total, self.n)

def main():
    var a = Acc(0, 0)
    a.total += 5
    a.n += 1
    a.total += 7
    a.n += 1
