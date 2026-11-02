def main():
    var l: List[Int] = [1, 2, 3]
    ref a = l[0]
    ref b = l[1]
    a += 10
    b += 20
    print(a, b, l[0], l[1], l[2])
