def main():
    var i = 0
    var s = 0
    while i < 4:
        var j = 0
        while j < i:
            s += i * j
            j += 1
        i += 1
    print(s)
