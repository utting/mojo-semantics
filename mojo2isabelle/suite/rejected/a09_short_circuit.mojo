def boom() -> Bool:
    print("boom")
    return True

def main():
    var a = False
    if a and boom():
        print("no")
    if not a or boom():
        print("yes")
