def swap(mut a: Int, mut b: Int):
    var t = a
    a = b
    b = t

def main():
    var l: List[Int] = [1, 2, 3]
    swap(l[0], l[2])
    print(l[0], l[1], l[2])
