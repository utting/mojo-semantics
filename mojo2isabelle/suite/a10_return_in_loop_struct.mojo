@fieldwise_init
struct R:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def f() -> Int:
    var r = R(1)
    var i = 0
    while i < 5:
        var q = R(10 + i)
        if i == 1:
            return i
        i += 1
    return 0

def main():
    print(f())
