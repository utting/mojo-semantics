def main():
    var m: List[List[Int]] = [[1, 2], [3]]
    m[1].append(4)
    m[0][1] = 9
    print(len(m), len(m[0]), len(m[1]), m[0][1], m[1][1])
