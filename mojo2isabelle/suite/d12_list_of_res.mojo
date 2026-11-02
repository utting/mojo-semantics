@fieldwise_init
struct Res:
    var id: Int
    def __deinit__(deinit self):
        print("drop", self.id)

def main():
    var l = List[Res]()
    l.append(Res(1))
    l.append(Res(2))
    l.append(Res(3))
    print(len(l))
    var r = l.pop()
    print("popped", r.id)
    print("end")
