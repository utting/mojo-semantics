def f(mut a: Int, b: Int):
    a += b

def main():
    var x = 1
    f(x, x)
    print(x)
