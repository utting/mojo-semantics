# micro-mojo-fuel: 10000
def fact(n: Int) -> Int:
    var acc = 1
    var i = 2
    while i <= n:
        acc *= i
        i += 1
    return acc

def classify(n: Int) -> Int:
    if n < 0:
        return -1
    elif n == 0:
        return 0
    else:
        return 1

def main():
    print(fact(5), classify(-4), classify(0), classify(9))
    var ok = 3 > 2 and not (1 >= 2)
    print(ok, 4 != 4, -7 - 1)
    var l = List[Int]()
    var i = 0
    while i < 4:
        l.append(i * i)
        i += 1
    print(l.pop(), len(l), l[2])
    print()
