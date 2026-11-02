def main():
    var a: List[Int] = [1, 2, 3]
    var b = a.copy()
    b.append(4)
    b[0] = 9
    print(len(a), len(b), a[0], b[0])
