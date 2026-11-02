@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

    def finish(var self):
        print("finish", self.id)

def main():
    var r = Res(1)
    r.finish()
    print(r.id)
