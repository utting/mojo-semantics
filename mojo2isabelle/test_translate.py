#!/usr/bin/env python3
"""Unit tests: programs outside micro-Mojo are rejected with a clear reason."""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mojo_translate import translate_source, TranslateError, Unsupported  # noqa: E402

MAIN = "def main():\n    pass\n"


def body(*lines):
    return "def main():\n" + "".join("    " + l + "\n" for l in lines)


# (program, expected exception class name fragment, substring of the message or reason)
REJECTS = [
    (body("for i in range(3):", "    print(i)"), "Unsupported", "'for' loop"),
    (body("while True:", "    break"), "Unsupported", "'break'"),
    (body("var x = 1.5"), "Unsupported", "float"),
    (body("var s = \"hi\""), "Unsupported", "string value"),
    (body("var x = 7 // 2"), "Unsupported", "operator '//'"),
    (body("var x = 99999999"), "Unsupported", "magnitude above"),
    (body("var x = 7 % 2"), "Unsupported", "operator '%'"),
    (body("var x: Float64 = 1"), "Unsupported", "type 'Float64'"),
    (body("var x = (1, 2)"), "Unsupported", "tuple"),
    (body("print(1, end=\"\")"), "Unsupported", "keyword argument"),
    (body("var l = [1, 2]", "print(l)"), "Unsupported", "printing a value of type List[Int]"),
    (body("try:", "    pass"), "Unsupported", "'try'"),
    ("import math\n" + MAIN, "Unsupported", "'import'"),
    ("from collections import Dict\n" + MAIN, "Unsupported", "'from"),
    ("def f[T: Copyable](x: T):\n    pass\n" + MAIN, "Unsupported", "parameterized function"),
    ("def f(owned x: Int):\n    pass\n" + MAIN, "Unsupported", "'owned'"),
    ("def f(x: Int = 3):\n    pass\n" + MAIN, "Unsupported", "default argument"),
    ("def f(*xs: Int):\n    pass\n" + MAIN, "Unsupported", "variadic"),
    ("trait T:\n    pass\n" + MAIN, "Unsupported", "'trait'"),
    ("@always_inline\ndef f():\n    pass\n" + MAIN, "Unsupported", "decorator '@always_inline'"),
    ("struct S(Hashable):\n    var x: Int\n" + MAIN, "Unsupported", "trait 'Hashable'"),
    ("struct S:\n    var x: Int\n    def __add__(self, o: Int) -> Int:\n        return 1\n" + MAIN, "Unsupported", "__add__"),
    ("struct S:\n    var x: Int\n    def __copyinit__(out self, other: Self):\n        self.x = 1\n" + MAIN, "Unsupported", "__copyinit__"),
    ("struct S[T: AnyType]:\n    var x: Int\n" + MAIN, "Unsupported", "parametric struct"),
    ("x = 1\n" + MAIN, "Unsupported", "top-level statement"),
    (body("var l: List[Int] = [1]", "var s = l[0:1]"), "Unsupported", "slice"),
    (body("var l = [1]", "var y = l.copy().pop()"), "Unsupported", "method call on a temporary"),
    (body("var x = 1", "var y = x if x < 2 else 3"), "SyntaxProblem", "expected end of line"),
    (body("if 1 < 2: pass"), "Unsupported", "one-line block"),
    (body("var x = 1", "x /= 2"), "Unsupported", "operator '/='"),
    (body("var a = 1", "var b = 2", "var c = a < b < 3"), "Unsupported", "chained comparison"),
    # not unsupported, but wrong
    (body("var x = y"), "TypeProblem", "unknown variable 'y'"),
    (body("var x = foo()"), "TypeProblem", "unknown function or struct 'foo'"),
    (body("var x: Int = True"), "TypeProblem", "has type Bool, expected Int"),
    (body("var l = []"), "TypeProblem", "cannot infer the element type"),
    ("def f() -> Int:\n    return 1\n", "TypeProblem", "no 'def main()'"),
    (body("\tvar x = 1"), "SyntaxProblem", "tab"),
]

ACCEPTS = [
    body("var x = 1", "x += 2", "print(x)"),
    body("var l = List[Int]()", "l.append(1)", "var e = l.pop()", "print(e, len(l))"),
    body("var b = 1 > 0 or 1 == 2", "if b:", "    print(\"yes\")", "else:", "    print(\"no\")"),
]


class Rejects(unittest.TestCase):
    def test_rejects(self):
        for src, cls, frag in REJECTS:
            with self.subTest(src=src, frag=frag):
                with self.assertRaises(TranslateError) as cm:
                    translate_source(src)
                e = cm.exception
                self.assertEqual(type(e).__name__, cls, e.format("t"))
                text = e.format("t")
                self.assertIn(frag, text)
                if cls == "Unsupported":
                    self.assertTrue(e.why, "an unsupported feature must come with an explanation: " + text)

    def test_accepts(self):
        for src in ACCEPTS:
            with self.subTest(src=src):
                translate_source(src)

    def test_error_format(self):
        with self.assertRaises(Unsupported) as cm:
            translate_source(body("for i in x:", "    pass"))
        self.assertTrue(cm.exception.format("p.mojo").startswith("p.mojo:2:5: unsupported Mojo feature: 'for' loop"))

    def test_gt_preserves_order(self):
        out = translate_source("def f() -> Int:\n    return 1\n" + body("print(f() > f())"))
        self.assertIn("ENot (EBin binop.Le", out.replace("\n", " ").replace("  ", " "))


if __name__ == "__main__":
    unittest.main()
