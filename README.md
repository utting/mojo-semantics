# A formal semantics for a subset of Mojo, in Isabelle

This repository formalises the memory-management rules of
[Mojo](https://www.modular.com/mojo) (value ownership, argument conventions,
references and origins, as-soon-as-possible destruction) in Isabelle/HOL, and
tests the formalisation against the real Mojo compiler.

It has three parts:

1. **A region model** of the memory-management ideas in
   [this gist](https://gist.github.com/nmsmith/cdaa94aa74e8e0611221e65db8e41f7b),
   with the design decisions and alternatives explained in the comments.
2. **Micro-Mojo**: a small subset of Mojo with abstract syntax, a big-step
   semantics, an ownership/type checker with ASAP destructor insertion, and a
   proof that the checker is sound.
3. **Differential testing**: a Python translator from `.mojo` files to
   Micro-Mojo terms, so that programs, and the output Mojo gives for them, can
   be evaluated in Isabelle.

## Theories

| theory | contents |
|--------|----------|
| `Mojo_Region_Model.thy` | region-based model of Mojo memory management, with rationale and alternatives |
| `Micro_Mojo_Syntax.thy` | the micro-Mojo subset, abstract syntax, Mojo-like syntactic sugar, example programs |
| `Micro_Mojo_Semantics.thy` | big-step interpreter (`run`, `eval`, `exec`) with a fuel bound and explicit errors |
| `Micro_Mojo_Static.thy` | static checker `check_prog` (types and ownership) and ASAP elaboration `elaborate`, which inserts `DROP`s |
| `Micro_Mojo_Soundness.thy` | soundness for expressions without calls |
| `Micro_Mojo_Soundness_Stmt.thy` | soundness for statements |
| `Micro_Mojo_Soundness_Calls.thy` | calls and whole programs; main theorem `run_safe` |

The main result: a program accepted by `check_prog` never fails with an
ownership or type error when run (only an out-of-range index, which Mojo also
reports at run time). Elaboration is proved to insert only drops; that elaborated programs are
still accepted by the checker is validated by the tests, not proved.

The `ROOT` file defines two sessions:

* `Mojo_Semantics`: the theories above;
* `Mojo_Tests` (in `tests/`): the differential tests.

## Building

Needs Isabelle2026.

```sh
export PATH="/Applications/Isabelle2026.app/bin:$PATH"
isabelle build -D . Mojo_Semantics      # definitions and soundness proofs (about a minute)
isabelle build -D . Mojo_Tests          # differential tests (about two minutes)
```

`setup.sh` shows how the Isabelle PIDE MCP server was set up for interactive
development with Claude Code.

## Differential testing

`mojo2isabelle/` holds the tools; see [its README](mojo2isabelle/README.md).

```
 .mojo programs ──translate──▶ Isabelle `prog` terms ─┐
       │                                               ├─▶ generated .thy ──isabelle build──▶ pass/fail
       └──mojo build + run──▶ *.expected.json ─────────┘
```

* `mojo_translate.py` parses a `.mojo` file and translates it to a term of
  type `prog`. Programs outside the subset are rejected, with an explanation of
  the unsupported feature.
* `mojo_suite.py` runs programs with the Mojo compiler (compile error, run-time
  error or output are recorded in `.expected.json`) and generates the test
  theories. Once the results are recorded, Mojo is not needed to rerun the tests.
* `mojo2isabelle/examples/` has the 11 example programs of the syntax theory;
  `mojo2isabelle/suite/` has 65 further programs (destruction timing, moves,
  copies, references, lists, parameter conventions, methods, arithmetic).
* Tests were recorded with Mojo 1.2.0. The semantics agrees with the compiler on
  all of them except the programs listed in `suite/known_divergences.json`.

### Known gaps

* `__deinit__` destroys fields individually, as soon as each is no longer
  needed. The model destroys all remaining fields after the body (tests d05, d13).
* Mojo short-circuits `and`/`or`; the model evaluates both operands, so the
  translator rejects programs where the right operand has effects.
* The checker requires distinct variable names within a function, while Mojo
  allows reuse in disjoint scopes; the translator rejects such programs.
* Integer literals above 10^6 are rejected (a numeral-evaluation problem on
  some Poly/ML platforms).

## Other files

* `hello-world/`: a `uv` project that installs the Mojo compiler
  (`uv run --project hello-world mojo ...`).
* `prompts.md`: the prompts used to develop this repository with Claude Code.
