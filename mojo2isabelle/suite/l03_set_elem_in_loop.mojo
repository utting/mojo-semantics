def main():
    var l: List[Int] = [0, 0, 0]
    var i = 0
    while i < len(l):
        l[i] = i * i
        i += 1
    print(l[0], l[1], l[2])
