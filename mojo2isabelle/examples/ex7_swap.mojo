def swap(mut a: Int, mut b: Int):
    var t = a
    a = b
    b = t

def main():
    var x = 1
    var y = 2
    swap(x, y)
    print(x, y)                 # 2 1
