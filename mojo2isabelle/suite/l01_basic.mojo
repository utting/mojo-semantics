def main():
    var l = List[Int]()
    print(len(l))
    l.append(3)
    l.append(4)
    print(len(l), l[0], l[1])
    var x = l.pop()
    print(x, len(l))
