#!/usr/bin/env python3
"""
mojo_suite.py -- differential-testing driver for the micro-Mojo semantics.

Workflow (see README.md):

  1. python3 mojo_suite.py check   tests/          which tests are in the subset?
  2. python3 mojo_suite.py run     tests/          run them with Mojo, record results
  3. python3 mojo_suite.py thy     tests/ -o ../Micro_Mojo_Tests.thy
  4. isabelle build -D .. Mojo_Tests               evaluate everything in batch mode

`run` stores the observed behaviour next to each test as NAME.expected.json:

    {"status": "ok" | "compile_error" | "runtime_error",
     "stdout": "...",              # standard output (status ok)
     "stderr": "...",              # compiler / runtime diagnostics (otherwise)
     "source": "mojo 1.0.0 ..." }  # what produced it ("hand-written" if by hand)

so that step 3 and 4 can be repeated without a Mojo installation.

A test may start with comment directives:

    # micro-mojo-fuel: 20000      evaluation fuel (default 5000)
"""
import argparse
import glob
import json
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mojo_translate import translate_source, TranslateError  # noqa: E402

DEFAULT_FUEL = 5000


def find_tests(path):
    if os.path.isdir(path):
        return sorted(glob.glob(os.path.join(path, "*.mojo")))
    return [path]


def expected_path(src):
    return os.path.splitext(src)[0] + ".expected.json"


def try_translate(src_path):
    """Returns (term, None) or (None, message)."""
    with open(src_path) as f:
        text = f.read()
    try:
        return translate_source(text), None
    except TranslateError as e:
        return None, e.format(os.path.basename(src_path))


# -- check ------------------------------------------------------------------

def cmd_check(args):
    bad = 0
    for p in sum((find_tests(x) for x in args.paths), []):
        term, err = try_translate(p)
        if err:
            bad += 1
            print(err)
        else:
            print("%s: ok" % os.path.basename(p))
    print("%d rejected" % bad, file=sys.stderr)
    return 1 if bad else 0


# -- run --------------------------------------------------------------------

def mojo_version(build_cmd):
    """Version string of the compiler used by BUILD_CMD (the words up to 'mojo', plus --version)."""
    words = build_cmd.split()
    cmd = (words[:words.index("mojo") + 1] if "mojo" in words else words[:1]) + ["--version"]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
        return r.stdout.strip() or r.stderr.strip()
    except Exception as e:  # pragma: no cover
        return "unknown (%s)" % e


def run_one(src_path, args, version):
    with tempfile.TemporaryDirectory() as tmp:
        exe = os.path.join(tmp, "prog")
        build = [a.format(src=src_path, out=exe) for a in args.build_cmd.split()]
        b = subprocess.run(build, capture_output=True, text=True, timeout=args.timeout)
        if b.returncode != 0:
            return {"status": "compile_error", "stdout": "", "stderr": b.stderr + b.stdout,
                    "source": version}
        r = subprocess.run([exe], capture_output=True, text=True, timeout=args.timeout)
        if r.returncode != 0:
            return {"status": "runtime_error", "stdout": r.stdout, "stderr": r.stderr,
                    "source": version}
        return {"status": "ok", "stdout": r.stdout, "stderr": r.stderr, "source": version}


def cmd_run(args):
    version = mojo_version(args.build_cmd)
    failures = 0
    for p in sum((find_tests(x) for x in args.paths), []):
        term, err = try_translate(p)
        if err and not args.all:
            print("skip %s (outside the subset; use --all to run anyway)" % os.path.basename(p))
            continue
        try:
            res = run_one(p, args, version)
        except FileNotFoundError as e:
            print("cannot run Mojo: %s\n(use --build-cmd to say how to build, e.g. 'mojo build {src} -o {out}')" % e,
                  file=sys.stderr)
            return 2
        except subprocess.TimeoutExpired:
            res = {"status": "runtime_error", "stdout": "", "stderr": "timeout", "source": version}
            failures += 1
        with open(expected_path(p), "w") as f:
            json.dump(res, f, indent=2)
            f.write("\n")
        print("%s: %s" % (os.path.basename(p), res["status"]))
    return 1 if failures else 0


# -- thy --------------------------------------------------------------------

def ident(stem):
    s = re.sub(r"[^A-Za-z0-9_]", "_", stem)
    return "t_" + s


def isa_line(s, what):
    for ch in s:
        if not (32 <= ord(ch) < 127) or ch in "'\\\"":
            raise ValueError("%s: output contains character %r that cannot be embedded in a theory" % (what, ch))
    return "''" + s + "''"


def fuel_of(text):
    m = re.search(r"^\s*#\s*micro-mojo-fuel:\s*(\d+)", text, re.M)
    return int(m.group(1)) if m else DEFAULT_FUEL


def comment_safe(text):
    return text.replace("(*", "( *").replace("*)", "* )")


HEADER = """\
(*
  %(theory)s.thy -- GENERATED by mojo2isabelle/mojo_suite.py; do not edit.

  Differential tests of the micro-Mojo semantics against the Mojo compiler:
  each test is a Mojo program (translated to Isabelle), together with the
  behaviour that Mojo showed (or, where marked, that was written by hand).
  `by eval` fails if the semantics and the compiler disagree.
*)

theory %(theory)s
  imports Micro_Mojo_Testing
begin
"""


def load_divergences(paths):
    """Known divergences: NAME -> reason, from known_divergences.json in the test directories."""
    div = {}
    for x in paths:
        d = x if os.path.isdir(x) else os.path.dirname(x) or "."
        f = os.path.join(d, "known_divergences.json")
        if os.path.exists(f):
            with open(f) as fh:
                div.update(json.load(fh))
    return div


def cmd_thy(args):
    out = [HEADER % {"theory": args.theory}]
    divergences = load_divergences(args.paths)
    skipped, n = [], 0
    names = {}
    for p in sum((find_tests(x) for x in args.paths), []):
        base = os.path.basename(p)
        stem = os.path.splitext(base)[0]
        with open(p) as f:
            text = f.read()
        term, err = try_translate(p)
        if err:
            skipped.append((base, "outside the subset: " + err.split("\n", 1)[0].split(": ", 1)[-1]))
            continue
        ep = expected_path(p)
        if not os.path.exists(ep):
            skipped.append((base, "no %s (run `mojo_suite.py run` first)" % os.path.basename(ep)))
            continue
        with open(ep) as f:
            exp = json.load(f)
        nm = ident(stem)
        if nm in names:
            raise SystemExit("test names %s and %s collide" % (names[nm], base))
        names[nm] = base
        fuel = fuel_of(text)
        lines = exp["stdout"].split("\n")
        if lines and lines[-1] == "":
            lines.pop()
        try:
            if exp["status"] == "ok":
                stmt = "test_output %s %d [%s]" % (nm, fuel, ", ".join(isa_line(l, base) for l in lines))
            elif exp["status"] == "compile_error":
                stmt = "test_compile_error %s" % nm
            elif exp["status"] == "runtime_error":
                stmt = "test_runtime_error %s %d" % (nm, fuel)
            else:
                raise ValueError("%s: unknown status %r" % (base, exp["status"]))
        except ValueError as e:
            skipped.append((base, str(e)))
            continue
        n += 1
        diverges = divergences.get(stem)
        out.append("subsection \\<open>%s\\<close>\n" % stem)
        out.append("text \\<open>Expected (%s): %s\\<close>\n" % (exp.get("source", "?"), exp["status"]))
        out.append("(* Mojo source:\n%s*)\n" % comment_safe(text if text.endswith("\n") else text + "\n"))
        out.append("definition %s :: prog where\n  \\<open>%s =\n%s\\<close>\n" % (
            nm, nm, "\n".join("    " + l for l in term.split("\n"))))
        if diverges:
            out.append("text \\<open>\\<^bold>\\<open>Known divergence from Mojo.\\<close> %s\n"
                       "  The lemma below asserts that the semantics does NOT yet reproduce the compiler's "
                       "behaviour; when the semantics is fixed it will fail and should be turned into a "
                       "normal test (remove the entry from known_divergences.json).\\<close>\n"
                       % diverges.replace("\\", "").replace("`", "'"))
            out.append("lemma %s_diverges: \\<open>\\<not> %s\\<close>\n  by eval\n" % (nm, stmt))
        else:
            out.append("lemma %s_test: \\<open>%s\\<close>\n  by eval\n" % (nm, stmt))
    if skipped:
        out.append("text \\<open>Skipped tests:\n%s\\<close>\n" % "\n".join(
            "  \\<^item> %s: %s" % (b, why.replace("\\", "").replace("\\<", "")) for b, why in skipped))
    out.append("end\n")
    with open(args.output, "w") as f:
        f.write("\n".join(out))
    print("wrote %d tests to %s" % (n, args.output))
    for b, why in skipped:
        print("skipped %s: %s" % (b, why), file=sys.stderr)
    return 1 if (skipped and args.strict) else 0


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("check", help="report which tests are within the subset")
    c.add_argument("paths", nargs="+")
    c.set_defaults(fn=cmd_check)
    r = sub.add_parser("run", help="run tests with the Mojo compiler and record the results")
    r.add_argument("paths", nargs="+")
    r.add_argument("--build-cmd", default="mojo build {src} -o {out}",
                   help="command that compiles a test ({src} source, {out} executable)")
    r.add_argument("--timeout", type=int, default=120)
    r.add_argument("--all", action="store_true", help="also run tests that the translator rejects")
    r.set_defaults(fn=cmd_run)
    t = sub.add_parser("thy", help="generate the Isabelle test theory")
    t.add_argument("paths", nargs="+")
    t.add_argument("-o", "--output", default="Micro_Mojo_Tests.thy")
    t.add_argument("--theory", default="Micro_Mojo_Tests", help="name of the generated theory")
    t.add_argument("--strict", action="store_true", help="fail if any test had to be skipped")
    t.set_defaults(fn=cmd_thy)
    args = ap.parse_args(argv)
    return args.fn(args)


if __name__ == "__main__":
    sys.exit(main())
