def append_twice(mut l: List[Int], other: List[Int]):
    l.append(len(other))
    l.append(len(other))

def main():
    var l: List[Int] = [0]
    var m = l.copy()
    append_twice(l, m)
    print(l[0], l[1], l[2])
    append_twice(l, l)          # error: argument aliasing
    print(l[3], l[4])
