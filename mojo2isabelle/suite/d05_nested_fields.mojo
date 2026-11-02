@fieldwise_init
struct Inner:
    var id: Int
    def __deinit__(deinit self):
        print("drop inner", self.id)

@fieldwise_init
struct Outer:
    var a: Inner
    var b: Inner
    var tag: Int
    def __deinit__(deinit self):
        print("drop outer", self.tag)

def main():
    var o = Outer(Inner(1), Inner(2), 9)
    print("built")
