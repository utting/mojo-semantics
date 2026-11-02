def swap(mut a: Int, mut b: Int):
    var t = a
    a = b
    b = t

def main():
    var x = 1
    swap(x, x)
    print(x)
