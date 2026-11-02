@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def consume(var r: Res):
    print("got", r.id)

def main():
    var a = Res(1)
    consume(a^)
    print(a.id)     # error: use of uninitialized value 'a'
