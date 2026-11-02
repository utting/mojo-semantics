@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var l = List[Res]()
    var a = Res(1)
    l.append(a^)
    print(len(l), l[0].id)
