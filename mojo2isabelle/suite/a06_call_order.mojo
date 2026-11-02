def show(n: Int) -> Int:
    print("show", n)
    return n

def main():
    var x = show(1) + show(2) * show(3)
    print(x)
    print(show(4), show(5))
