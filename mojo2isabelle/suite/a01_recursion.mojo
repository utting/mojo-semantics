def fib(n: Int) -> Int:
    if n < 2:
        return n
    return fib(n - 1) + fib(n - 2)

def main():
    print(fib(10), fib(1), fib(0))
