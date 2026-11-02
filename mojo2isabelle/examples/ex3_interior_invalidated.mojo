def main():
    var list: List[Int] = [1, 2, 3]
    ref elem = list[0]
    list.append(4)  # may reallocate, so `elem` is invalidated
    print(elem)     # error: use of invalidated interior reference
