def dangle(ref a: Int) -> ref[a] Int:
    var local = 5
    return local          # error: reference to a local escapes

def main():
    var x = 1
    ref r = dangle(x)
    print(r)
