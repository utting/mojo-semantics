def f(n: Int) -> Int:
    var i = 0
    while True:
        if i * i > n:
            return i
        i += 1
    return -1

def main():
    print(f(10), f(100))
