def main():
    var list: List[Int] = [1, 2, 3]
    ref elem = list[0]
    elem = 7
    list[1] += 10
    print(elem, list[0], list[1], len(list))
