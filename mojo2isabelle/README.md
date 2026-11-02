# mojo2isabelle: differential testing of the micro-Mojo semantics

Tools for checking the Isabelle semantics (`../Micro_Mojo_*.thy`) against the
real Mojo compiler. Python 3.8+, no dependencies.

```
 tests/*.mojo ──translate──▶ Isabelle `prog` terms ─┐
      │                                              ├─▶ Micro_Mojo_Tests.thy ──isabelle build──▶ pass/fail
      └──mojo build + run──▶ *.expected.json ────────┘
```

## Files

| file | purpose |
|------|---------|
| `mojo_translate.py` | parser + translator: `.mojo` → term of type `prog`; rejects anything outside the subset with a reason |
| `mojo_suite.py` | driver: `check` (subset test), `run` (compile+run with Mojo, record results), `thy` (generate the theory) |
| `test_translate.py` | unit tests for the translator, mainly the rejection messages (`python3 test_translate.py`) |
| `examples/` | the example programs of `Micro_Mojo_Syntax.thy` as `.mojo` files + `.expected.json` |
| `../tests/Micro_Mojo_Testing.thy` | `test_output`, `test_compile_error`, `test_runtime_error`, and output rendering |
| `../tests/Micro_Mojo_Tests.thy` | **generated** test theory (session `Mojo_Tests`) |
| `../tests/Micro_Mojo_Translation_Check.thy` | proves the translator output equals the hand-written encodings |

## Usage

```sh
cd mojo2isabelle
python3 mojo_translate.py examples/ex4_point.mojo          # print the Isabelle term
python3 mojo_translate.py --check prog.mojo                # in the subset?
python3 mojo_suite.py check examples/                      # which tests are accepted/rejected
python3 mojo_suite.py run   examples/                      # needs `mojo` on PATH; writes *.expected.json
python3 mojo_suite.py run   examples/ --build-cmd 'uv run --project ../hello-world mojo build {src} -o {out}'   # Mojo installed via uv
python3 mojo_suite.py thy   examples/ -o ../tests/Micro_Mojo_Tests.thy
cd .. && isabelle build -D . Mojo_Tests                    # batch evaluation
```

`run` compiles with `mojo build {src} -o {out}` (change with `--build-cmd`),
then runs the binary. A failed build is recorded as `compile_error`, a
non-zero exit of the binary as `runtime_error`, otherwise `ok` plus stdout.
Results are stored in `NAME.expected.json`, so `thy` and the Isabelle build can
be repeated on machines without Mojo.

The `.expected.json` files in `examples/` were recorded with **Mojo 1.2.0**
(via `uv run mojo`). They agree with the outputs we had first written by hand,
and the compile errors are the intended ones (use of uninitialized value,
invalidated interior reference, uninitialized field, argument aliasing,
reference to a local escaping), so the semantics matches the compiler on all
11 examples.

## What a test asserts

All programs are run after ASAP elaboration (`elaborate`), as Mojo destroys
values right after their last use.

* `status: ok` → `test_output P fuel [lines]`: the Isabelle checker
  `check_prog` accepts `P`, and running it prints exactly the compiler's lines.
  Output is compared as text: `print(a, b)` renders as `a b`, `Bool` as
  `True`/`False`.
* `status: compile_error` → `test_compile_error P`: `check_prog` rejects `P`
  (the message is not compared).
* `status: runtime_error` → `test_runtime_error P fuel`: the checker accepts
  `P` but execution ends with `ErrBounds`.

A disagreement shows up as a failed `by eval`; `value "actual_output t_NAME 5000"`
in a scratch theory shows what the semantics does instead.

Per-test fuel: put `# micro-mojo-fuel: N` at the top of the `.mojo` file
(default 5000).

## What the translator accepts

Types `Int`, `Bool`, `List[T]`, structs; `def`/`fn`; conventions default/`read`,
`mut`, `var`, `ref`; `-> T`, `-> ref[a, b] T`; `var`, `ref`, assignment
(`= += -= *=`), calls and method calls as statements, `if/elif/else`,
`while`, `return`, `pass`, `print(...)`; expressions with `+ - *`,
`< <= == > >= !=`, `and or not`, unary `-`, `p^`, `p.copy()`, `len(p)`,
`[a, b]`, `List[T]()`, `p.append(e)`, `p.pop()`. Structs: fields, `@fieldwise_init`,
`(Copyable)`, `__init__(out self, ...)`, `__deinit__(deinit self)`, methods.

Anything else is rejected, e.g.

```
t.mojo:3:5: unsupported Mojo feature: 'for' loop
    micro-Mojo has no iteration protocol; write a 'while' loop instead
```

Only the first problem in a file is reported (syntax-level rejections come
before type-level ones).

## Things to keep in mind

* **Integer overflow.** Mojo's `Int` is 64-bit and wraps; the model uses
  unbounded integers. Literals above 10^6 in magnitude are rejected (also because Isabelle's
  `eval` hangs on huge numerals on this 32-bit Poly/ML platform), but
  overflowing arithmetic cannot be detected statically: keep test values small.
* **Desugarings.** `a > b` becomes `not (a <= b)`, `a != b` becomes
  `not (a == b)` and `-e` becomes `0 - e`, all preserving evaluation order.
  `p += e` is only accepted when `p` contains no calls (it would be evaluated
  twice). `and`/`or` are not short-circuiting in the model, so a test whose
  right operand has side effects would differ from Mojo.
* **String literals** are only allowed as direct `print` arguments, and must
  be printable ASCII without `'`, `"` or `\`.
* **Only the first compile error** matters for `compile_error` tests; the
  model does not distinguish *why* the compiler rejected the program, so a test
  can pass for the wrong reason. Compare diagnostics by hand when it matters.
* **Compile errors vs. language drift.** The translator is conservative: it
  accepts `def` and `fn`, and `read` as well as the default convention. Syntax
  that the installed Mojo does not accept will show up as a `compile_error`
  result for a test that the model expects to run.
