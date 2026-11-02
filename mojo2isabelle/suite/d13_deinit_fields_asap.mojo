@fieldwise_init
struct Inner:
    var id: Int
    def __deinit__(deinit self):
        print("drop inner", self.id)

@fieldwise_init
struct Outer:
    var a: Inner
    var b: Inner
    var c: Inner
    def __deinit__(deinit self):
        print("outer start")
        print("a is", self.a.id)
        print("outer mid")
        print("b is", self.b.id)
        print("outer end")

def main():
    var o = Outer(Inner(1), Inner(2), Inner(3))
    print("built")
