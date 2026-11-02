#!/usr/bin/env python3
"""
mojo_translate.py -- translate a *.mojo program in the micro-Mojo subset into
a term of type `prog` of the Isabelle theory Micro_Mojo_Syntax.

    python3 mojo_translate.py prog.mojo            # print the Isabelle term
    python3 mojo_translate.py --check prog.mojo    # only report accept/reject

Programs outside the subset are rejected with an error of the form

    prog.mojo:12:9: unsupported Mojo feature: 'for' loop
        micro-Mojo has no iteration protocol; write a 'while' loop instead

(exit status 1).  Programs that are not even valid in the subset's syntax
(or are ill-typed in the ways the translator needs to notice, e.g. a call of
an unknown function) are reported as 'error:' instead of 'unsupported'.

The translator does NOT check ownership rules: that is the job of the Isabelle
checker `check_prog`, and of the Mojo compiler we compare against.  It only
needs enough type information to fill in the types that Mojo infers but the
abstract syntax records (`var x = e`), and to check the few type restrictions
the abstract syntax relies on (e.g. only Int/Bool/string values are printed).

Subset summary (see Micro_Mojo_Syntax.thy for the abstract syntax):

  types        Int, Bool, List[T], structs declared in the file
  top level    struct and def (or fn) declarations; `def main():` is required
  struct       fields `var f: T`; optional @fieldwise_init; optional
               (Copyable) trait; optional __init__(out self, ...); optional
               __deinit__(deinit self); methods with self conventions
               (default, mut, var, ref)
  parameters   default / read / imm, mut, var, ref conventions
  returns      nothing, a value type, or `-> ref[a, b] T`
  statements   var, ref, assignment (also += -= *=), expression statements,
               if/elif/else, while, return, pass, print(...)
  expressions  int/bool literals, string literals (only as print arguments),
               places x, p.f, p[i], transfer p^, p.copy(), calls (also
               constructors), method calls p.m(...), len(p), [a, b, c],
               List[T](), + - * < <= == > >= != and or not, unary -
"""
import re
import sys
import argparse

# --------------------------------------------------------------------------
# Errors
# --------------------------------------------------------------------------


class TranslateError(Exception):
    """Base class: carries a source position and a message."""
    kind = "error"

    def __init__(self, pos, msg, why=None):
        Exception.__init__(self, msg)
        self.pos = pos
        self.msg = msg
        self.why = why

    def format(self, filename):
        line, col = self.pos
        head = "%s:%d:%d: %s: %s" % (filename, line, col, self.kind, self.msg)
        if self.why:
            head += "\n    " + self.why
        return head


class Unsupported(TranslateError):
    kind = "unsupported Mojo feature"


class SyntaxProblem(TranslateError):
    kind = "syntax error"


class TypeProblem(TranslateError):
    kind = "error"


# Explanations for constructs that are outside micro-Mojo, keyed by keyword.
KEYWORD_WHY = {
    "for": ("'for' loop", "micro-Mojo has no iteration protocol; write a 'while' loop instead"),
    "break": ("'break'", "micro-Mojo has no break/continue; restructure the loop condition"),
    "continue": ("'continue'", "micro-Mojo has no break/continue; restructure the loop condition"),
    "try": ("'try' statement", "micro-Mojo has no exceptions (no raises/try/except)"),
    "except": ("'except' clause", "micro-Mojo has no exceptions (no raises/try/except)"),
    "raise": ("'raise' statement", "micro-Mojo has no exceptions (no raises/try/except)"),
    "finally": ("'finally' clause", "micro-Mojo has no exceptions"),
    "raises": ("'raises' effect", "micro-Mojo has no exceptions"),
    "match": ("'match' statement", "pattern matching is not part of micro-Mojo; use if/elif/else"),
    "lambda": ("lambda expression", "micro-Mojo has no closures"),
    "import": ("'import' statement", "micro-Mojo programs are single-file and use only the prelude (Int, Bool, List)"),
    "from": ("'from ... import' statement", "micro-Mojo programs are single-file and use only the prelude (Int, Bool, List)"),
    "comptime": ("'comptime' declaration", "compile-time evaluation is not part of micro-Mojo"),
    "alias": ("'alias' declaration", "compile-time aliases are not part of micro-Mojo"),
    "trait": ("'trait' declaration", "user-defined traits are not part of micro-Mojo (only the Copyable marker)"),
    "with": ("'with' statement", "context managers are not part of micro-Mojo"),
    "async": ("'async'", "asynchronous code is not part of micro-Mojo"),
    "await": ("'await'", "asynchronous code is not part of micro-Mojo"),
    "del": ("'del' statement", "explicit deletion is expressed with the transfer operator or is implicit (ASAP destruction)"),
    "global": ("'global' statement", "micro-Mojo has no global variables"),
    "assert": ("'assert' statement", "assertions are not part of micro-Mojo"),
    "yield": ("'yield'", "generators are not part of micro-Mojo"),
    "class": ("'class' declaration", "Mojo has no classes; use 'struct'"),
    "is": ("'is' operator", "identity comparison is not part of micro-Mojo"),
    "in": ("'in' operator", "membership tests are not part of micro-Mojo"),
    "owned": ("'owned' convention", "removed in Mojo 1.0; use 'var'"),
    "inout": ("'inout' convention", "removed in Mojo 1.0; use 'mut'"),
    "borrowed": ("'borrowed' convention", "removed in Mojo 1.0; use the default or 'read'"),
}

KEYWORDS = {
    "def", "fn", "struct", "var", "ref", "if", "elif", "else", "while", "return",
    "pass", "and", "or", "not", "True", "False", "out", "mut", "deinit",
} | set(KEYWORD_WHY)

# --------------------------------------------------------------------------
# Tokenizer
# --------------------------------------------------------------------------

TOK_RE = re.compile(r"""
    (?P<ws>[ ]+)
  | (?P<comment>\#[^\n]*)
  | (?P<float>\d+\.\d*|\.\d+|\d+[eE][+-]?\d+)
  | (?P<hex>0[xXbBoO][0-9a-fA-F_]+)
  | (?P<int>\d[\d_]*)
  | (?P<name>[A-Za-z_][A-Za-z_0-9]*)
  | (?P<str>"(?:[^"\\\n]|\\.)*"|'(?:[^'\\\n]|\\.)*')
  | (?P<op>->|==|!=|<=|>=|\+=|-=|\*=|//=|/=|%=|//|\*\*|<<|>>|[-+*/%<>=!:,.()\[\]{}^@&|~;])
""", re.X)


class Tok(object):
    __slots__ = ("kind", "val", "line", "col")

    def __init__(self, kind, val, line, col):
        self.kind, self.val, self.line, self.col = kind, val, line, col

    def pos(self):
        return (self.line, self.col)

    def __repr__(self):
        return "Tok(%s,%r)" % (self.kind, self.val)


def tokenize(src):
    """Produce NEWLINE / INDENT / DEDENT / name / int / str / op / EOF tokens."""
    toks = []
    indents = [0]
    depth = 0           # bracket nesting: newlines inside are insignificant
    lines = src.split("\n")
    for lineno, text in enumerate(lines, 1):
        if "\t" in text[:len(text) - len(text.lstrip())]:
            raise SyntaxProblem((lineno, 1), "tab in indentation",
                                "use spaces for indentation")
        if depth == 0:
            stripped = text.strip()
            if stripped == "" or stripped.startswith("#"):
                continue
            ind = len(text) - len(text.lstrip(" "))
            if ind > indents[-1]:
                indents.append(ind)
                toks.append(Tok("INDENT", "", lineno, 1))
            else:
                while ind < indents[-1]:
                    indents.pop()
                    toks.append(Tok("DEDENT", "", lineno, 1))
                if ind != indents[-1]:
                    raise SyntaxProblem((lineno, 1), "inconsistent dedent")
        pos = 0
        while pos < len(text):
            m = TOK_RE.match(text, pos)
            if not m:
                ch = text[pos]
                if text.startswith('"""', pos) or text.startswith("'''", pos):
                    raise Unsupported((lineno, pos + 1), "triple-quoted string",
                                      "docstrings and multi-line strings are not part of micro-Mojo")
                raise SyntaxProblem((lineno, pos + 1), "unexpected character %r" % ch)
            kind = m.lastgroup
            val = m.group(kind)
            col = pos + 1
            pos = m.end()
            if kind in ("ws", "comment"):
                continue
            if kind == "op":
                if val in "([":
                    depth += 1
                elif val in ")]":
                    depth -= 1
            if kind == "str" and (text.startswith('"""', col - 1) or text.startswith("'''", col - 1)):
                raise Unsupported((lineno, col), "triple-quoted string",
                                  "docstrings and multi-line strings are not part of micro-Mojo")
            toks.append(Tok(kind, val, lineno, col))
        if depth == 0:
            toks.append(Tok("NEWLINE", "", lineno, len(text) + 1))
    last = len(lines)
    while len(indents) > 1:
        indents.pop()
        toks.append(Tok("DEDENT", "", last, 1))
    toks.append(Tok("EOF", "", last, 1))
    return toks


# --------------------------------------------------------------------------
# Surface AST (positions kept for error messages)
# --------------------------------------------------------------------------


class N(object):
    """Generic AST node: kind, fields, position."""

    def __init__(self, kind, pos, **kw):
        self.kind = kind
        self.pos = pos
        self.__dict__.update(kw)

    def __repr__(self):
        return "N(%s)" % ", ".join("%s=%r" % kv for kv in self.__dict__.items())


# --------------------------------------------------------------------------
# Parser
# --------------------------------------------------------------------------


class Parser(object):
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    # -- helpers
    @property
    def t(self):
        return self.toks[self.i]

    def peek(self, k=1):
        return self.toks[min(self.i + k, len(self.toks) - 1)]

    def next(self):
        t = self.t
        self.i += 1
        return t

    def is_op(self, v):
        return self.t.kind == "op" and self.t.val == v

    def is_name(self, v):
        return self.t.kind == "name" and self.t.val == v

    def accept_op(self, v):
        if self.is_op(v):
            return self.next()
        return None

    def accept_name(self, v):
        if self.is_name(v):
            return self.next()
        return None

    def expect_op(self, v):
        if not self.is_op(v):
            self.fail("expected '%s'" % v)
        return self.next()

    def expect_name(self, v):
        if not self.is_name(v):
            self.fail("expected '%s'" % v)
        return self.next()

    def fail(self, msg):
        t = self.t
        found = {"NEWLINE": "end of line", "INDENT": "indent", "DEDENT": "dedent",
                 "EOF": "end of file"}.get(t.kind, repr(t.val))
        self.check_keyword(t)
        raise SyntaxProblem(t.pos(), "%s, found %s" % (msg, found))

    def check_keyword(self, t):
        if t.kind == "name" and t.val in KEYWORD_WHY:
            feat, why = KEYWORD_WHY[t.val]
            raise Unsupported(t.pos(), feat, why)

    def ident(self, what="identifier"):
        t = self.t
        if t.kind != "name":
            self.fail("expected %s" % what)
        self.check_keyword(t)
        if t.val in KEYWORDS:
            raise SyntaxProblem(t.pos(), "'%s' is a keyword and cannot be used as %s" % (t.val, what))
        self.next()
        return t

    def newline(self):
        if self.t.kind == "NEWLINE":
            self.next()
        elif self.t.kind in ("DEDENT", "EOF"):
            pass
        else:
            self.fail("expected end of line")

    # -- types
    def parse_type(self):
        t = self.t
        if t.kind != "name":
            self.fail("expected a type")
        self.check_keyword(t)
        self.next()
        if self.is_op("["):
            if t.val != "List":
                raise Unsupported(t.pos(), "parametric type '%s[...]'" % t.val,
                                  "generics are not part of micro-Mojo; only List[T] is built in")
            self.next()
            elem = self.parse_type()
            if self.is_op(","):
                raise Unsupported(self.t.pos(), "extra type parameters",
                                  "List takes exactly one type parameter in micro-Mojo")
            self.expect_op("]")
            return N("tlist", t.pos(), elem=elem)
        return N("tname", t.pos(), name=t.val)

    # -- expressions (precedence climbing)
    def parse_expr(self):
        return self.parse_or()

    def parse_or(self):
        e = self.parse_and()
        while self.is_name("or"):
            p = self.next().pos()
            e = N("bin", p, op="or", l=e, r=self.parse_and())
        return e

    def parse_and(self):
        e = self.parse_not()
        while self.is_name("and"):
            p = self.next().pos()
            e = N("bin", p, op="and", l=e, r=self.parse_not())
        return e

    def parse_not(self):
        if self.is_name("not"):
            p = self.next().pos()
            return N("not", p, e=self.parse_not())
        return self.parse_cmp()

    CMP = ("<", "<=", "==", ">", ">=", "!=")

    def parse_cmp(self):
        e = self.parse_add()
        if self.t.kind == "op" and self.t.val in self.CMP:
            t = self.next()
            r = self.parse_add()
            if self.t.kind == "op" and self.t.val in self.CMP:
                raise Unsupported(self.t.pos(), "chained comparison",
                                  "write 'a < b and b < c' instead of 'a < b < c'")
            e = N("bin", t.pos(), op=t.val, l=e, r=r)
        return e

    def parse_add(self):
        e = self.parse_mul()
        while self.t.kind == "op" and self.t.val in ("+", "-"):
            t = self.next()
            e = N("bin", t.pos(), op=t.val, l=e, r=self.parse_mul())
        return e

    def parse_mul(self):
        e = self.parse_unary()
        while self.t.kind == "op" and self.t.val in ("*", "/", "//", "%", "**", "<<", ">>", "&", "|"):
            t = self.next()
            e = N("bin", t.pos(), op=t.val, l=e, r=self.parse_unary())
        return e

    def parse_unary(self):
        if self.is_op("-"):
            p = self.next().pos()
            e = self.parse_unary()
            if e.kind == "int":
                return N("int", p, val=-e.val)
            return N("neg", p, e=e)
        if self.is_op("+"):
            self.fail("unary '+' is not supported")
        if self.is_op("~"):
            raise Unsupported(self.t.pos(), "bitwise operator '~'", "bit operations are not part of micro-Mojo")
        return self.parse_postfix()

    def parse_args(self):
        """After '(' : positional arguments only."""
        args = []
        if not self.is_op(")"):
            while True:
                if self.is_op("*") or self.is_op("**"):
                    raise Unsupported(self.t.pos(), "variadic argument",
                                      "micro-Mojo has no *args/**kwargs")
                if self.t.kind == "name" and self.peek().kind == "op" and self.peek().val == "=":
                    raise Unsupported(self.t.pos(), "keyword argument '%s='" % self.t.val,
                                      "micro-Mojo calls take positional arguments only")
                args.append(self.parse_expr())
                if not self.accept_op(","):
                    break
                if self.is_op(")"):
                    break
        self.expect_op(")")
        return args

    def parse_postfix(self):
        e = self.parse_atom()
        while True:
            if self.is_op("."):
                self.next()
                name = self.ident("a field or method name")
                if self.is_op("("):
                    p = self.next().pos()
                    args = self.parse_args()
                    e = N("mcall", name.pos(), recv=e, name=name.val, args=args)
                else:
                    e = N("field", name.pos(), base=e, name=name.val)
            elif self.is_op("["):
                p = self.next().pos()
                if e.kind == "name" and e.name == "List":
                    ty = self.parse_type()
                    self.expect_op("]")
                    e = N("typeapp", p, name="List", ty=ty)
                    continue
                idx = self.parse_expr()
                if self.is_op(":") or self.is_op(","):
                    raise Unsupported(self.t.pos(), "slice or multi-index",
                                      "micro-Mojo supports only single integer indices")
                self.expect_op("]")
                e = N("index", p, base=e, idx=idx)
            elif self.is_op("("):
                p = self.next().pos()
                args = self.parse_args()
                e = N("call", p, fn=e, args=args)
            elif self.is_op("^"):
                nxt = self.peek()
                if nxt.kind == "NEWLINE" or (nxt.kind == "op" and nxt.val in (")", ",", "]")):
                    p = self.next().pos()
                    e = N("take", p, e=e)
                else:
                    raise Unsupported(self.t.pos(), "bitwise xor '^'",
                                      "'^' is only supported as the postfix transfer operator 'x^'")
            else:
                return e

    def parse_atom(self):
        t = self.t
        if t.kind == "int":
            self.next()
            return N("int", t.pos(), val=int(t.val.replace("_", "")))
        if t.kind in ("float", "hex"):
            raise Unsupported(t.pos(), "float/hex/binary literal %s" % t.val,
                              "only decimal Int literals are part of micro-Mojo")
        if t.kind == "str":
            self.next()
            return N("str", t.pos(), val=t.val[1:-1], raw=t.val)
        if t.kind == "name":
            if t.val == "True" or t.val == "False":
                self.next()
                return N("bool", t.pos(), val=(t.val == "True"))
            if t.val in ("None",):
                raise Unsupported(t.pos(), "'None'", "Optional values are not part of micro-Mojo")
            self.check_keyword(t)
            if t.val in KEYWORDS:
                self.fail("expected an expression")
            self.next()
            return N("name", t.pos(), name=t.val)
        if t.kind == "op" and t.val == "(":
            self.next()
            e = self.parse_expr()
            if self.is_op(","):
                raise Unsupported(self.t.pos(), "tuple", "tuples are not part of micro-Mojo")
            self.expect_op(")")
            return e
        if t.kind == "op" and t.val == "[":
            self.next()
            items = []
            if not self.is_op("]"):
                while True:
                    items.append(self.parse_expr())
                    if self.is_name("for"):
                        raise Unsupported(self.t.pos(), "list comprehension",
                                          "micro-Mojo has no 'for'; build the list with append in a 'while' loop")
                    if not self.accept_op(","):
                        break
                    if self.is_op("]"):
                        break
            self.expect_op("]")
            return N("list", t.pos(), items=items)
        if t.kind == "op" and t.val == "{":
            raise Unsupported(t.pos(), "dict/set literal", "dictionaries and sets are not part of micro-Mojo")
        self.fail("expected an expression")

    # -- statements
    def parse_block(self):
        """':' NEWLINE INDENT stmts DEDENT"""
        self.expect_op(":")
        if self.t.kind != "NEWLINE":
            raise Unsupported(self.t.pos(), "one-line block",
                              "put the body on its own indented lines")
        self.next()
        if self.t.kind != "INDENT":
            self.fail("expected an indented block")
        self.next()
        stmts = []
        while self.t.kind != "DEDENT" and self.t.kind != "EOF":
            stmts.append(self.parse_stmt())
        if self.t.kind == "DEDENT":
            self.next()
        return stmts

    def parse_stmt(self):
        t = self.t
        if t.kind == "name":
            v = t.val
            if v == "var":
                self.next()
                name = self.ident("a variable name")
                ty = None
                init = None
                if self.accept_op(":"):
                    ty = self.parse_type()
                if self.accept_op("="):
                    init = self.parse_expr()
                if ty is None and init is None:
                    raise SyntaxProblem(name.pos(), "'var %s' needs a type or an initial value" % name.val)
                if self.is_op(","):
                    raise Unsupported(self.t.pos(), "multiple declarations / tuple unpacking",
                                      "declare one variable per statement")
                self.newline()
                return N("var", t.pos(), name=name.val, ty=ty, init=init)
            if v == "ref":
                self.next()
                name = self.ident("a reference name")
                if self.is_op(":"):
                    raise Unsupported(self.t.pos(), "type annotation on a 'ref' binding",
                                      "write 'ref r = e'; the type is inferred")
                self.expect_op("=")
                init = self.parse_expr()
                self.newline()
                return N("ref", t.pos(), name=name.val, init=init)
            if v == "if":
                return self.parse_if()
            if v == "while":
                self.next()
                c = self.parse_expr()
                body = self.parse_block()
                if self.is_name("else"):
                    raise Unsupported(self.t.pos(), "'while ... else'", "loop else-clauses are not part of micro-Mojo")
                return N("while", t.pos(), cond=c, body=body)
            if v == "return":
                self.next()
                e = None
                if self.t.kind != "NEWLINE":
                    e = self.parse_expr()
                self.newline()
                return N("return", t.pos(), e=e)
            if v == "pass":
                self.next()
                self.newline()
                return N("pass", t.pos())
            if v in ("def", "fn", "struct"):
                raise Unsupported(t.pos(), "nested %s declaration" % v,
                                  "declarations are only allowed at the top level")
            self.check_keyword(t)
        e = self.parse_expr()
        if self.t.kind == "op" and self.t.val in ("=", "+=", "-=", "*="):
            op = self.next()
            rhs = self.parse_expr()
            self.newline()
            return N("assign", op.pos(), op=op.val, lhs=e, rhs=rhs)
        if self.t.kind == "op" and self.t.val in ("/=", "//=", "%="):
            raise Unsupported(self.t.pos(), "operator '%s'" % self.t.val,
                              "only + - * are part of micro-Mojo's Int arithmetic")
        if self.is_op(":"):
            raise Unsupported(self.t.pos(), "annotation without 'var'",
                              "declare variables with 'var x: T'")
        if self.is_op(","):
            raise Unsupported(self.t.pos(), "tuple expression / multiple assignment",
                              "tuples are not part of micro-Mojo")
        self.newline()
        return N("expr", e.pos, e=e)

    def parse_if(self):
        t = self.next()   # 'if' or 'elif'
        c = self.parse_expr()
        body = self.parse_block()
        orelse = []
        if self.is_name("elif"):
            orelse = [self.parse_if()]
        elif self.is_name("else"):
            self.next()
            orelse = self.parse_block()
        return N("if", t.pos(), cond=c, body=body, orelse=orelse)

    # -- declarations
    def parse_param(self, is_method_first):
        """Returns N('param', conv, name, ty)."""
        conv = "imm"
        t = self.t
        if t.kind == "name" and t.val in ("mut", "var", "ref", "out", "deinit", "read", "imm"):
            nxt = self.peek()
            if nxt.kind == "name":      # a convention word followed by the name
                self.next()
                conv = {"read": "imm"}.get(t.val, t.val)
        elif t.kind == "op" and t.val in ("*", "**"):
            raise Unsupported(t.pos(), "variadic parameter", "micro-Mojo has no *args/**kwargs")
        elif t.kind == "name" and t.val in ("owned", "inout", "borrowed"):
            self.check_keyword(t)
        name = self.ident("a parameter name")
        ty = None
        if self.accept_op(":"):
            ty = self.parse_type()
            if conv == "ref" and self.is_op("["):
                raise Unsupported(self.t.pos(), "parametric 'ref' origin",
                                  "origins of parameters are inferred in micro-Mojo")
        if self.is_op("="):
            raise Unsupported(self.t.pos(), "default argument value",
                              "micro-Mojo parameters have no defaults")
        return N("param", name.pos(), conv=conv, name=name.val, ty=ty)

    def parse_params(self):
        self.expect_op("(")
        ps = []
        if not self.is_op(")"):
            while True:
                ps.append(self.parse_param(not ps))
                if not self.accept_op(","):
                    break
                if self.is_op(")"):
                    break
        self.expect_op(")")
        return ps

    def parse_ret(self):
        """After the params: optional '-> T' / '-> ref[a,b] T'."""
        if self.is_name("raises"):
            self.check_keyword(self.t)
        if not self.accept_op("->"):
            return None
        if self.is_name("ref"):
            self.next()
            origins = []
            if self.accept_op("["):
                while True:
                    origins.append(self.ident("an origin (a parameter name)").val)
                    if not self.accept_op(","):
                        break
                self.expect_op("]")
            else:
                raise Unsupported(self.t.pos(), "'ref' return without explicit origin",
                                  "write '-> ref[param, ...] T'")
            ty = self.parse_type()
            return N("retref", ty.pos, origins=origins, ty=ty)
        if self.is_name("raises"):
            self.check_keyword(self.t)
        ty = self.parse_type()
        return N("retval", ty.pos, ty=ty)

    def parse_def(self, decorators):
        kw = self.next()    # def / fn
        name = self.ident("a function name")
        if self.is_op("["):
            raise Unsupported(self.t.pos(), "parameterized function '%s[...]'" % name.val,
                              "generics / compile-time parameters are not part of micro-Mojo")
        params = self.parse_params()
        ret = self.parse_ret()
        if self.is_name("raises"):
            self.check_keyword(self.t)
        body = self.parse_block()
        return N("def", kw.pos(), name=name.val, params=params, ret=ret, body=body,
                 decorators=decorators, npos=name.pos())

    def parse_struct(self, decorators):
        kw = self.next()
        name = self.ident("a struct name")
        if self.is_op("["):
            raise Unsupported(self.t.pos(), "parametric struct '%s[...]'" % name.val,
                              "generics are not part of micro-Mojo")
        traits = []
        if self.accept_op("("):
            while not self.is_op(")"):
                tr = self.ident("a trait name")
                traits.append(tr)
                if not self.accept_op(","):
                    break
            self.expect_op(")")
        self.expect_op(":")
        if self.t.kind != "NEWLINE":
            raise Unsupported(self.t.pos(), "one-line block", "put the body on its own indented lines")
        self.next()
        if self.t.kind != "INDENT":
            self.fail("expected an indented block")
        self.next()
        fields, methods = [], []
        while self.t.kind not in ("DEDENT", "EOF"):
            decs = self.parse_decorators()
            if self.is_name("var"):
                self.next()
                f = self.ident("a field name")
                self.expect_op(":")
                ty = self.parse_type()
                if self.is_op("="):
                    raise Unsupported(self.t.pos(), "field default value",
                                      "initialize fields in __init__ (or use @fieldwise_init)")
                self.newline()
                if decs:
                    raise Unsupported(decs[0].pos, "decorator '@%s' on a field" % decs[0].name, "")
                fields.append((f.val, ty, f.pos()))
            elif self.is_name("def") or self.is_name("fn"):
                methods.append(self.parse_def(decs))
            elif self.is_name("pass"):
                self.next()
                self.newline()
            else:
                self.check_keyword(self.t)
                self.fail("expected a field ('var f: T') or a method ('def ...')")
        if self.t.kind == "DEDENT":
            self.next()
        return N("struct", kw.pos(), name=name.val, traits=traits, fields=fields,
                 methods=methods, decorators=decorators, npos=name.pos())

    def parse_decorators(self):
        decs = []
        while self.is_op("@"):
            p = self.next().pos()
            n = self.ident("a decorator name")
            if self.is_op("("):
                raise Unsupported(self.t.pos(), "decorator arguments", "")
            self.newline()
            decs.append(N("dec", p, name=n.val))
        return decs

    def parse_module(self):
        defs = []
        while self.t.kind != "EOF":
            if self.t.kind == "NEWLINE":
                self.next()
                continue
            if self.t.kind == "INDENT":
                self.fail("unexpected indent")
            decs = self.parse_decorators()
            if self.is_name("struct"):
                defs.append(self.parse_struct(decs))
            elif self.is_name("def") or self.is_name("fn"):
                defs.append(self.parse_def(decs))
            else:
                self.check_keyword(self.t)
                raise Unsupported(self.t.pos(), "top-level statement",
                                  "micro-Mojo programs consist only of struct and def declarations")
        return defs


# --------------------------------------------------------------------------
# Isabelle term construction
# --------------------------------------------------------------------------

def isa_str(s, pos):
    """HOL string literal ''...''; restrict to what is safe in Isabelle text."""
    for ch in s:
        if not (32 <= ord(ch) < 127) or ch in "'\\\"":
            raise Unsupported(pos, "character %r in a string literal" % ch,
                              "string literals are limited to printable ASCII without quotes or backslashes "
                              "(so that they can be embedded in an Isabelle theory unchanged)")
    return "''" + s + "''"


class T(object):
    """A pretty-printable term: head applied to arguments (strings or T)."""

    def __init__(self, head, *args):
        self.head = head
        self.args = list(args)

    def flat(self):
        if not self.args:
            return self.head
        return "%s %s" % (self.head, " ".join(a.flat_arg() if isinstance(a, (T, L)) else a
                                              for a in self.args))

    def flat_arg(self):
        return self.head if not self.args else "(" + self.flat() + ")"


class L(object):
    """A list term [a, b, c]."""

    def __init__(self, items):
        self.items = items

    def flat(self):
        return "[" + ", ".join(i.flat() if isinstance(i, (T, L)) else i for i in self.items) + "]"

    def flat_arg(self):
        return self.flat()


def render(x, indent=0, width=96):
    """Pretty-print T/L/str with line breaking when too wide."""
    if isinstance(x, str):
        return x
    f = x.flat()
    if len(f) + indent <= width:
        return f
    pad = " " * (indent + 2)
    if isinstance(x, L):
        inner = ",\n".join(pad + render(i, indent + 2, width) for i in x.items)
        return "[\n" + inner + "]"
    parts = []
    for a in x.args:
        if isinstance(a, T) and a.args:
            parts.append("(" + render(a, indent + 3, width) + ")")
        elif isinstance(a, T):
            parts.append(a.head)
        elif isinstance(a, L):
            parts.append(render(a, indent + 2, width))
        else:
            parts.append(a)
    return x.head + "\n" + "\n".join(pad + p for p in parts)


def flat(x):
    return x if isinstance(x, str) else x.flat()


def mk_int(n):
    return T("EInt", "(%d)" % n if n < 0 else str(n))


# --------------------------------------------------------------------------
# Types of the translator (just names)
# --------------------------------------------------------------------------

INT_LIMIT = 10 ** 6
INT, BOOL, STR, NONE = ("Int",), ("Bool",), ("Str",), ("None",)


def tlist(t):
    return ("List", t)


def show_ty(t):
    if t[0] == "List":
        return "List[%s]" % show_ty(t[1])
    if t[0] == "Struct":
        return t[1]
    return t[0]


def ty_term(t):
    if t == INT:
        return "TInt"
    if t == BOOL:
        return "TBool"
    if t == STR:
        return "TStr"
    if t == NONE:
        return "TNone"
    if t[0] == "List":
        return T("TList", ty_term(t[1]))
    return T("TStruct", isa_raw_str(t[1]))


def isa_raw_str(s):
    return "''" + s + "''"


# constructors are qualified: Mojo_Region_Model also has e.g. effect.Mut
CONV = {"imm": "conv.Imm", "mut": "conv.Mut", "var": "conv.Var", "ref": "conv.Ref",
        "out": "conv.Out", "deinit": "conv.Deinit"}

# --------------------------------------------------------------------------
# Translator: surface AST -> Isabelle term, with light type inference
# --------------------------------------------------------------------------


class FunSig(object):
    def __init__(self, name, params, ret):
        self.name, self.params, self.ret = name, params, ret   # params: [(conv, name, ty)]; ret: ('none',)|('val',ty)|('ref',origins,ty)


class Translator(object):
    def __init__(self, defs):
        self.defs = defs
        self.structs = {}      # name -> dict(fields=[(n,ty)], methods={name: FunSig}, node)
        self.funs = {}         # name -> FunSig
        self.scopes = []       # stack of dict name -> type
        self.cur_ret = None
        self.fun_names = set()

    # -- types
    def conv_type(self, tn):
        if tn.kind == "tlist":
            return tlist(self.conv_type(tn.elem))
        n = tn.name
        if n == "Int":
            return INT
        if n == "Bool":
            return BOOL
        if n in self.structs:
            return ("Struct", n)
        if n in ("Float64", "Float32", "Float16", "BFloat16", "SIMD", "String", "StringLiteral", "UInt",
                 "UInt8", "UInt16", "UInt32", "UInt64", "Int8", "Int16", "Int32", "Int64", "Dict", "Set",
                 "Optional", "Tuple", "Pointer", "UnsafePointer", "Span", "Self", "Some"):
            raise Unsupported(tn.pos, "type '%s'" % n,
                              "micro-Mojo has only Int, Bool, List[T] and the structs declared in the program")
        raise TypeProblem(tn.pos, "unknown type '%s'" % n,
                          "declare it with 'struct %s:' or use Int, Bool or List[T]" % n)

    # -- declarations
    def collect(self):
        # struct names first so that field/parameter types may refer to any struct
        for d in self.defs:
            if d.kind == "struct":
                if d.name in self.structs:
                    raise TypeProblem(d.npos, "duplicate struct '%s'" % d.name)
                if d.name in ("Int", "Bool", "List"):
                    raise TypeProblem(d.npos, "struct '%s' shadows a builtin type" % d.name)
                self.structs[d.name] = dict(fields=[], methods={}, node=d)
        for d in self.defs:
            if d.kind == "struct":
                st = self.structs[d.name]
                for (f, tn, pos) in d.fields:
                    if any(f == g for g, _ in st["fields"]):
                        raise TypeProblem(pos, "duplicate field '%s'" % f)
                    st["fields"].append((f, self.conv_type(tn)))
        for d in self.defs:
            if d.kind == "struct":
                self.collect_struct(d)
            else:
                if d.name in self.funs or d.name in self.structs:
                    raise TypeProblem(d.npos, "duplicate definition of '%s'" % d.name)
                self.check_decorators(d.decorators, d.npos)
                self.funs[d.name] = self.fun_sig(d, None)

    def check_decorators(self, decs, pos, allowed=()):
        for dec in decs:
            if dec.name not in allowed:
                raise Unsupported(dec.pos, "decorator '@%s'" % dec.name,
                                  "micro-Mojo supports only @fieldwise_init on structs")

    def ret_sig(self, d):
        r = d.ret
        if r is None:
            return ("none",)
        if r.kind == "retval":
            return ("val", self.conv_type(r.ty))
        return ("ref", list(r.origins), self.conv_type(r.ty))

    def fun_sig(self, d, struct_ty):
        params = []
        seen = set()
        for i, p in enumerate(d.params):
            if p.name in seen:
                raise TypeProblem(p.pos, "duplicate parameter '%s'" % p.name)
            seen.add(p.name)
            if p.conv in ("out", "deinit") and not (struct_ty and i == 0):
                raise Unsupported(p.pos, "'%s' convention on parameter '%s'" % (p.conv, p.name),
                                  "'out' and 'deinit' are only supported for 'self' of __init__ / __deinit__")
            if p.ty is None:
                if struct_ty and i == 0 and p.name == "self":
                    ty = struct_ty
                else:
                    raise TypeProblem(p.pos, "parameter '%s' needs a type annotation" % p.name)
            else:
                ty = self.conv_type(p.ty)
                if struct_ty and i == 0 and p.name == "self":
                    raise Unsupported(p.pos, "explicit type on 'self'", "write plain 'self'")
            params.append((p.conv, p.name, ty))
        return FunSig(d.name, params, self.ret_sig(d))

    def collect_struct(self, d):
        st = self.structs[d.name]
        self.check_decorators(d.decorators, d.npos, allowed=("fieldwise_init",))
        d.fieldwise = any(x.name == "fieldwise_init" for x in d.decorators)
        d.copyable = False
        for tr in d.traits:
            if tr.val == "Copyable":
                d.copyable = True
            elif tr.val in ("Movable", "ImplicitlyDestructible", "Writable"):
                if tr.val == "Writable":
                    raise Unsupported(tr.pos(), "trait 'Writable'", "printing structs is not part of micro-Mojo")
            else:
                raise Unsupported(tr.pos(), "trait '%s'" % tr.val,
                                  "only the Copyable (and Movable) markers are supported")
        sty = ("Struct", d.name)
        d.init = None
        d.deinit = None
        d.meths = []
        for m in d.methods:
            self.check_decorators(m.decorators, m.npos)
            if m.name in ("__copyinit__", "__moveinit__"):
                raise Unsupported(m.npos, m.name, "user-defined copy/move constructors are not part of micro-Mojo")
            if m.name.startswith("__") and m.name not in ("__init__", "__deinit__"):
                raise Unsupported(m.npos, "special method %s" % m.name,
                                  "operator overloading and other dunder methods are not part of micro-Mojo")
            if not m.params or m.params[0].name != "self":
                raise Unsupported(m.npos, "method '%s' without 'self'" % m.name,
                                  "static methods are not part of micro-Mojo")
            if m.name == "__init__":
                if d.init:
                    raise Unsupported(m.npos, "overloaded __init__", "micro-Mojo has at most one __init__")
                if m.params[0].conv != "out":
                    raise TypeProblem(m.npos, "__init__ must declare 'out self'")
                if m.ret is not None:
                    raise TypeProblem(m.npos, "__init__ cannot have a return type")
                if d.fieldwise:
                    raise TypeProblem(m.npos, "@fieldwise_init conflicts with an explicit __init__")
                d.init = m
                m.sig = self.fun_sig(m, sty)
            elif m.name == "__deinit__":
                if d.deinit:
                    raise Unsupported(m.npos, "overloaded __deinit__", "")
                if len(m.params) != 1 or m.params[0].conv != "deinit":
                    raise TypeProblem(m.npos, "__deinit__ must be declared '__deinit__(deinit self)'")
                if m.ret is not None:
                    raise TypeProblem(m.npos, "__deinit__ cannot have a return type")
                d.deinit = m
                m.sig = self.fun_sig(m, sty)
            else:
                if m.name in st["methods"]:
                    raise Unsupported(m.npos, "overloaded method '%s'" % m.name, "overloading is not part of micro-Mojo")
                if m.params[0].conv in ("out", "deinit"):
                    raise Unsupported(m.params[0].pos, "'%s self' on a method" % m.params[0].conv, "")
                m.sig = self.fun_sig(m, sty)
                st["methods"][m.name] = m.sig
                d.meths.append(m)

    # -- scopes
    def push(self):
        self.scopes.append({})

    def pop(self):
        self.scopes.pop()

    def declare(self, name, ty, pos=None):
        if name in self.fun_names and pos is not None:
            raise Unsupported(pos, "variable name '%s' declared twice in one function" % name,
                              "the micro-Mojo checker requires every variable name to be unique within a "
                              "function (no shadowing, no reuse in disjoint scopes); rename one of them")
        self.fun_names.add(name)
        self.scopes[-1][name] = ty

    def lookup(self, name, pos):
        for s in reversed(self.scopes):
            if name in s:
                return s[name]
        raise TypeProblem(pos, "unknown variable '%s'" % name)

    # -- purity (no calls: safe to duplicate or reorder)
    def pure(self, e):
        k = e.kind
        if k in ("int", "bool", "str", "name"):
            return True
        if k in ("call", "mcall"):
            return k == "call" and e.fn.kind == "name" and e.fn.name == "len" and all(self.pure(a) for a in e.args)
        if k == "field":
            return self.pure(e.base)
        if k == "index":
            return self.pure(e.base) and self.pure(e.idx)
        if k == "bin":
            return self.pure(e.l) and self.pure(e.r)
        if k in ("not", "neg", "take"):
            return self.pure(e.e)
        if k == "list":
            return all(self.pure(i) for i in e.items)
        return False

    def no_effects(self, e):
        """No calls (except len) and no indexing: evaluation can neither print nor fail."""
        k = e.kind
        if k in ("int", "bool", "str", "name"):
            return True
        if k == "call":
            return e.fn.kind == "name" and e.fn.name == "len" and all(self.no_effects(a) for a in e.args)
        if k == "field":
            return self.no_effects(e.base)
        if k == "bin":
            return self.no_effects(e.l) and self.no_effects(e.r)
        if k in ("not", "neg"):
            return self.no_effects(e.e)
        return False

    # -- places
    def is_place(self, e):
        return e.kind == "name" or (e.kind == "field" and self.is_place(e.base)) \
            or (e.kind == "index" and self.is_place(e.base))

    def place(self, e):
        """Return (isabelle place term, type)."""
        if e.kind == "name":
            ty = self.lookup(e.name, e.pos)
            return T("PVar", isa_raw_str(e.name)), ty
        if e.kind == "field":
            p, ty = self.place(e.base) if self.is_place(e.base) else self.bad_place(e.base)
            if ty[0] != "Struct":
                raise TypeProblem(e.pos, "field access '.%s' on a value of type %s" % (e.name, show_ty(ty)))
            for (f, fty) in self.structs[ty[1]]["fields"]:
                if f == e.name:
                    return T("PField", p, isa_raw_str(f)), fty
            raise TypeProblem(e.pos, "struct %s has no field '%s'" % (ty[1], e.name))
        if e.kind == "index":
            p, ty = self.place(e.base) if self.is_place(e.base) else self.bad_place(e.base)
            if ty[0] != "List":
                raise TypeProblem(e.pos, "indexing a value of type %s" % show_ty(ty),
                                  "only List[T] can be indexed")
            ie, ity = self.expr(e.idx)
            if ity != INT:
                raise TypeProblem(e.idx.pos, "list index must be Int, not %s" % show_ty(ity))
            return T("PIndex", p, ie), ty[1]
        raise TypeProblem(e.pos, "expected a variable, field or element here")

    def bad_place(self, e):
        raise Unsupported(e.pos, "field/element access on a temporary",
                          "micro-Mojo can only access fields and elements of variables; "
                          "bind the value with 'var'/'ref' first")

    # -- expressions
    def expr(self, e, in_print=False):
        k = e.kind
        if k == "int":
            if abs(e.val) > INT_LIMIT:
                raise Unsupported(e.pos, "integer literal %d with magnitude above %d" % (e.val, INT_LIMIT),
                                  "Mojo's Int is 64-bit while the Isabelle model uses unbounded integers; "
                                  "and Isabelle's `eval` does not terminate on very large numerals on 32-bit "
                                  "Poly/ML platforms. Keep test values small")
            return mk_int(e.val), INT
        if k == "bool":
            return T("EBool", "True" if e.val else "False"), BOOL
        if k == "str":
            if not in_print:
                raise Unsupported(e.pos, "string value",
                                  "micro-Mojo has no String type; string literals may only be direct arguments of print")
            return T("EStr", isa_str(e.val, e.pos)), STR
        if k in ("name", "field", "index"):
            p, ty = self.place(e)
            return T("EPlace", p), ty
        if k == "take":
            if not self.is_place(e.e):
                raise Unsupported(e.pos, "transfer '^' of a non-variable",
                                  "only places (x, x.f, x[i]) can be transferred")
            p, ty = self.place(e.e)
            return T("ETake", p), ty
        if k == "neg":
            a, ty = self.expr(e.e)
            self.want(ty, INT, e.e.pos, "operand of unary '-'")
            return T("EBin", "binop.Sub", mk_int(0), a), INT
        if k == "not":
            a, ty = self.expr(e.e)
            self.want(ty, BOOL, e.e.pos, "operand of 'not'")
            return T("ENot", a), BOOL
        if k == "bin":
            return self.binop(e)
        if k == "list":
            if not e.items:
                raise TypeProblem(e.pos, "cannot infer the element type of '[]'",
                                  "declare the list with a type: 'var l: List[Int] = []'")
            terms, ty0 = [], None
            for it in e.items:
                t, ty = self.expr(it)
                if ty0 is None:
                    ty0 = ty
                self.want(ty, ty0, it.pos, "list element")
                terms.append(t)
            return T("EList", L(terms)), tlist(ty0)
        if k == "call":
            return self.call(e)
        if k == "mcall":
            return self.mcall(e)
        if k == "typeapp":
            raise TypeProblem(e.pos, "'List[...]' must be called: 'List[T]()'")
        raise TypeProblem(e.pos, "unsupported expression")

    def want(self, ty, expected, pos, what):
        if ty != expected:
            raise TypeProblem(pos, "%s has type %s, expected %s" % (what, show_ty(ty), show_ty(expected)))

    def binop(self, e):
        op = e.op
        if op in ("/", "//", "%", "**"):
            raise Unsupported(e.pos, "operator '%s'" % op,
                              "only + - * and comparisons are part of micro-Mojo "
                              "(division/modulo can fail and are not modelled)")
        if op in ("<<", ">>", "&", "|"):
            raise Unsupported(e.pos, "bitwise operator '%s'" % op, "bit operations are not part of micro-Mojo")
        a, ta = self.expr(e.l)
        b, tb = self.expr(e.r)
        names = {"+": "binop.Add", "-": "binop.Sub", "*": "binop.Mul", "<": "binop.Lt",
                 "<=": "binop.Le", "==": "binop.Eq", "and": "binop.And", "or": "binop.Or"}
        if op in ("+", "-", "*"):
            self.want(ta, INT, e.l.pos, "left operand of '%s'" % op)
            self.want(tb, INT, e.r.pos, "right operand of '%s'" % op)
            return T("EBin", names[op], a, b), INT
        if op in ("<", "<=", ">", ">="):
            self.want(ta, INT, e.l.pos, "left operand of '%s'" % op)
            self.want(tb, INT, e.r.pos, "right operand of '%s'" % op)
            if op in ("<", "<="):
                return T("EBin", names[op], a, b), BOOL
            # a > b  ==  not (a <= b);  a >= b  ==  not (a < b): keeps evaluation order
            return T("ENot", T("EBin", "binop.Le" if op == ">" else "binop.Lt", a, b)), BOOL
        if op in ("==", "!="):
            if ta != tb or ta not in (INT, BOOL):
                raise Unsupported(e.pos, "'%s' on %s and %s" % (op, show_ty(ta), show_ty(tb)),
                                  "equality is only supported between two Ints or two Bools")
            t = T("EBin", "binop.Eq", a, b)
            return (t if op == "==" else T("ENot", t)), BOOL
        if op in ("and", "or"):
            if not self.no_effects(e.r):
                raise Unsupported(e.r.pos, "right operand of '%s' with calls or indexing" % op,
                                  "Mojo short-circuits 'and'/'or' but the micro-Mojo semantics evaluates both "
                                  "operands; use nested 'if' statements when the right operand has side effects "
                                  "or can fail")
            self.want(ta, BOOL, e.l.pos, "left operand of '%s'" % op)
            self.want(tb, BOOL, e.r.pos, "right operand of '%s'" % op)
            return T("EBin", names[op], a, b), BOOL
        raise TypeProblem(e.pos, "unsupported operator '%s'" % op)

    def args_for(self, e, sig, params):
        if len(e.args) != len(params):
            raise TypeProblem(e.pos, "'%s' expects %d argument(s), got %d" % (sig.name, len(params), len(e.args)))
        out = []
        for a, (conv, pname, pty) in zip(e.args, params):
            t, ty = self.expr(a)
            self.want(ty, pty, a.pos, "argument '%s' of '%s'" % (pname, sig.name))
            out.append(t)
        return out

    def call(self, e):
        fn = e.fn
        if fn.kind == "typeapp":
            if e.args:
                raise Unsupported(e.pos, "List[T](...) with arguments",
                                  "only the empty constructor 'List[T]()' is supported; use a list literal")
            ty = tlist(self.conv_type(fn.ty))
            return T("EList", L([])), ty
        if fn.kind != "name":
            raise Unsupported(e.pos, "call of a non-name expression",
                              "only named functions, structs and methods can be called")
        n = fn.name
        if n == "len":
            if len(e.args) != 1:
                raise TypeProblem(e.pos, "len() takes exactly one argument")
            a = e.args[0]
            if not self.is_place(a):
                raise Unsupported(a.pos, "len() of a temporary", "len() is only supported on variables, fields and elements")
            p, ty = self.place(a)
            if ty[0] != "List":
                raise TypeProblem(a.pos, "len() of type %s" % show_ty(ty), "only List[T] has a length")
            return T("ELen", p), INT
        if n == "print":
            raise Unsupported(e.pos, "print() used as an expression", "print is a statement in micro-Mojo")
        if n in self.structs:
            st = self.structs[n]
            d = st["node"]
            if d.init:
                params = d.init.sig.params[1:]
                sig = d.init.sig
            elif d.fieldwise:
                params = [("imm", f, ty) for f, ty in st["fields"]]
                sig = FunSig(n, [], None)
                sig.name = n
            else:
                raise TypeProblem(e.pos, "struct '%s' has no __init__ and is not @fieldwise_init" % n)
            args = self.args_for(e, sig, params)
            return T("ECall", isa_raw_str(n), L(args)), ("Struct", n)
        if n in self.funs:
            sig = self.funs[n]
            args = self.args_for(e, sig, sig.params)
            return T("ECall", isa_raw_str(n), L(args)), self.ret_type(sig)
        if n in ("String", "Float64", "Int64", "Int32", "Int8", "UInt", "SIMD", "Dict", "Set", "Optional", "range",
                 "abs", "min", "max", "sqrt", "pow", "int", "str", "float", "bool", "Bool", "Int", "String", "assert_equal"):
            raise Unsupported(e.pos, "call of builtin '%s'" % n,
                              "micro-Mojo has no standard library beyond len(), print() and List methods")
        raise TypeProblem(e.pos, "unknown function or struct '%s'" % n)

    def ret_type(self, sig):
        r = sig.ret
        if r[0] == "none":
            return NONE
        return r[1] if r[0] == "val" else r[2]

    def mcall(self, e):
        recv = e.recv
        if not self.is_place(recv):
            raise Unsupported(e.pos, "method call on a temporary",
                              "the receiver of a method call must be a variable, field or element; "
                              "bind the value with 'var'/'ref' first")
        p, ty = self.place(recv)
        m = e.name
        if m == "copy" and not e.args:
            return T("ECopy", p), ty
        if ty[0] == "List":
            if m == "append":
                if len(e.args) != 1:
                    raise TypeProblem(e.pos, "append() takes exactly one argument")
                a, aty = self.expr(e.args[0])
                self.want(aty, ty[1], e.args[0].pos, "argument of append")
                return T("EMeth", p, isa_raw_str("append"), L([a])), NONE
            if m == "pop":
                if e.args:
                    raise Unsupported(e.pos, "pop(index)", "only pop() without arguments is supported")
                return T("EMeth", p, isa_raw_str("pop"), L([])), ty[1]
            raise Unsupported(e.pos, "List method '%s'" % m,
                              "only append(), pop(), copy() and len() are supported on lists")
        if ty[0] == "Struct":
            sigs = self.structs[ty[1]]["methods"]
            if m not in sigs:
                raise TypeProblem(e.pos, "struct %s has no method '%s'" % (ty[1], m))
            sig = sigs[m]
            args = self.args_for(e, sig, sig.params[1:])
            return T("EMeth", p, isa_raw_str(m), L(args)), self.ret_type(sig)
        raise TypeProblem(e.pos, "method call '.%s()' on a value of type %s" % (m, show_ty(ty)))

    # -- statements
    def block(self, stmts):
        """Translate a block (new scope) to a list of stmt terms."""
        self.push()
        out = []
        for s in stmts:
            out.extend(self.stmt(s))
        self.pop()
        return out

    @staticmethod
    def seq(terms):
        if not terms:
            return "SPass"
        if len(terms) == 1:
            return terms[0]
        return T("seq", L(terms))

    def stmt(self, s):
        k = s.kind
        if k == "pass":
            return []
        if k == "var":
            ty = self.conv_type(s.ty) if s.ty else None
            init = None
            if s.init is not None:
                if s.init.kind == "list" and not s.init.items and ty is not None:
                    init, ity = T("EList", L([])), ty
                else:
                    init, ity = self.expr(s.init)
                if ty is None:
                    ty = ity
                self.want(ity, ty, s.init.pos, "initializer of '%s'" % s.name)
                if ity == NONE:
                    raise TypeProblem(s.init.pos, "initializer has no value")
            self.declare(s.name, ty, s.pos)
            return [T("SVar", isa_raw_str(s.name), ty_term(ty),
                      T("Some", init) if init is not None else "None")]
        if k == "ref":
            init, ity = self.expr(s.init)
            if s.init.kind not in ("name", "field", "index", "call") or \
                    (s.init.kind == "call" and not (s.init.fn.kind == "name" and s.init.fn.name in self.funs
                                                      and self.funs[s.init.fn.name].ret[0] == "ref")):
                raise TypeProblem(s.init.pos, "a 'ref' binding needs a place or a call returning 'ref'")
            self.declare(s.name, ity, s.pos)
            return [T("SRef", isa_raw_str(s.name), init)]
        if k == "assign":
            if not self.is_place(s.lhs):
                raise Unsupported(s.lhs.pos, "assignment to a non-place",
                                  "only variables, fields and list elements can be assigned")
            p, pty = self.place(s.lhs)
            r, rty = self.expr(s.rhs)
            if s.op == "=":
                self.want(rty, pty, s.rhs.pos, "assigned value")
                return [T("SAssign", p, r)]
            self.want(pty, INT, s.lhs.pos, "target of '%s'" % s.op)
            self.want(rty, INT, s.rhs.pos, "operand of '%s'" % s.op)
            if not self.pure(s.lhs):
                raise Unsupported(s.lhs.pos, "'%s' on a place with side effects" % s.op,
                                  "the place would be evaluated twice in the translation; "
                                  "write 'p = p + e' with a call-free place")
            opn = {"+=": "binop.Add", "-=": "binop.Sub", "*=": "binop.Mul"}[s.op]
            return [T("SAssign", p, T("EBin", opn, T("EPlace", p), r))]
        if k == "expr":
            e = s.e
            if e.kind == "call" and e.fn.kind == "name" and e.fn.name == "print":
                return [self.print_stmt(e)]
            if e.kind not in ("call", "mcall"):
                raise Unsupported(e.pos, "expression statement",
                                  "only calls and method calls can be used as statements")
            t, ty = self.expr(e)
            return [T("SExpr", t)]
        if k == "if":
            c, cty = self.expr(s.cond)
            self.want(cty, BOOL, s.cond.pos, "condition")
            a = self.block(s.body)
            b = self.block(s.orelse)
            return [T("SIf", c, self.seq(a), self.seq(b))]
        if k == "while":
            c, cty = self.expr(s.cond)
            self.want(cty, BOOL, s.cond.pos, "condition")
            return [T("SWhile", c, self.seq(self.block(s.body)))]
        if k == "return":
            return [self.return_stmt(s)]
        raise TypeProblem(s.pos, "unsupported statement")

    def print_stmt(self, e):
        items = []
        for a in e.args:
            t, ty = self.expr(a, in_print=True)
            if ty not in (INT, BOOL, STR):
                raise Unsupported(a.pos, "printing a value of type %s" % show_ty(ty),
                                  "micro-Mojo can only print Int, Bool and string literals")
            items.append(t)
        return T("SPrint", L(items))

    def return_stmt(self, s):
        r = self.cur_ret
        if r is None or r[0] == "none":
            if s.e is not None:
                raise TypeProblem(s.pos, "return with a value in a function that returns nothing")
            return "SReturn None"
        if s.e is None:
            raise TypeProblem(s.pos, "return without a value in a function with a return type")
        t, ty = self.expr(s.e)
        want = r[1] if r[0] == "val" else r[2]
        self.want(ty, want, s.e.pos, "returned value")
        return T("SReturn", T("Some", t))

    # -- functions and program
    @staticmethod
    def tup3(a, b, c):
        return "(%s, %s, %s)" % (a, b, flat(c))

    def fun_term(self, name, sig, body, params=None, ret=None):
        params = sig.params if params is None else params
        ps = L([self.tup3(CONV[c], isa_raw_str(n), ty_term(ty)) for (c, n, ty) in params])
        r = sig.ret
        if r[0] == "none":
            rt = "RNone"
        elif r[0] == "val":
            rt = T("RVal", ty_term(r[1]))
        else:
            rt = T("RRef", L([isa_raw_str(o) for o in r[1]]), ty_term(r[2]))
        return T("Fun", isa_raw_str(name), ps, rt, body)

    def check_origins(self, d, sig):
        if sig.ret[0] == "ref":
            names = [n for (_, n, _) in sig.params]
            for o in sig.ret[1]:
                if o not in names:
                    raise TypeProblem(d.ret.pos, "origin '%s' is not a parameter of '%s'" % (o, d.name),
                                      "in micro-Mojo, origins of 'ref' returns are parameter names")

    def translate_fun(self, d, sig):
        self.check_origins(d, sig)
        self.scopes = [{}]
        self.fun_names = set()
        for (c, n, ty) in sig.params:
            self.declare(n, ty)
        self.cur_ret = sig.ret
        body = self.seq(self.block(d.body))
        return self.fun_term(d.name, sig, body)

    def translate_struct(self, d):
        st = self.structs[d.name]
        fields = L(["(%s, %s)" % (isa_raw_str(f), flat(ty_term(ty))) for f, ty in st["fields"]])
        init = "None"
        if d.init:
            init = T("Some", self.translate_fun(d.init, d.init.sig))
        deinit = "None"
        if d.deinit:
            self.scopes = [{"self": ("Struct", d.name)}]
            self.fun_names = {"self"}
            self.cur_ret = ("none",)
            deinit = T("Some", self.seq(self.block(d.deinit.body)))
        meths = L([self.translate_fun(m, m.sig) for m in d.meths])
        return T("Struct", isa_raw_str(d.name), fields,
                 "True" if d.copyable else "False", "True" if d.fieldwise else "False",
                 init, deinit, meths)

    def translate(self):
        self.collect()
        main = self.funs.get("main")
        if main is None:
            raise TypeProblem((1, 1), "no 'def main()' function",
                              "a micro-Mojo program must define 'def main():'")
        if main.params:
            raise TypeProblem((1, 1), "main must take no parameters")
        if main.ret != ("none",):
            raise Unsupported((1, 1), "main with a return type", "main must not return a value")
        structs, funs = [], []
        for d in self.defs:
            if d.kind == "struct":
                structs.append(self.translate_struct(d))
            else:
                funs.append(self.translate_fun(d, self.funs[d.name]))
        return T("Prog", L(structs), L(funs))


# --------------------------------------------------------------------------
# API
# --------------------------------------------------------------------------

def translate_source(src):
    """Mojo source text -> Isabelle term text for a `prog`.  Raises TranslateError."""
    toks = tokenize(src)
    defs = Parser(toks).parse_module()
    term = Translator(defs).translate()
    return render(term)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Translate micro-Mojo programs to Isabelle")
    ap.add_argument("file")
    ap.add_argument("--check", action="store_true", help="only check that the program is in the subset")
    ap.add_argument("--name", help="emit 'definition NAME :: prog where ...'")
    args = ap.parse_args(argv)
    with open(args.file) as f:
        src = f.read()
    try:
        term = translate_source(src)
    except TranslateError as e:
        sys.stderr.write(e.format(args.file) + "\n")
        return 1
    if args.check:
        print("%s: in the micro-Mojo subset" % args.file)
    elif args.name:
        print("definition %s :: prog where\n  \\<open>%s = %s\\<close>" % (args.name, args.name, term))
    else:
        print(term)
    return 0


if __name__ == "__main__":
    sys.exit(main())
