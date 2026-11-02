@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def eat(var r: Res):
    print("eat", r.id)

def main():
    var a = Res(1)
    var c = False
    if c:
        eat(a^)
    else:
        eat(a^)
    print("end")
