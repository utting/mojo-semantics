def fill(mut l: List[Int], n: Int):
    var i = 0
    while i < n:
        l.append(i)
        i += 1

def total(l: List[Int]) -> Int:
    var s = 0
    var i = 0
    while i < len(l):
        s += l[i]
        i += 1
    return s

def main():
    var l = List[Int]()
    fill(l, 5)
    print(len(l), total(l))
