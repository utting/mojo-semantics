def main():
    var l: List[Int] = [5, 6, 7]
    var i = 1
    ref e = l[i + 1]
    e = 0
    print(l[0], l[1], l[2])
