struct Point:
    var x: Int
    var y: Int

    def __init__(out self, a: Int):
        self.x = a      # error: field 'y' not initialized

def main():
    var p = Point(3)
    print(p.x)
