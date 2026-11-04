#!/bin/sh
# Regenerates paper/snippets-*.tex from the Isabelle theories, so that the
# declarations and equations quoted in the paper follow the theory sources.
# Run from the repository root:  sh paper/make-snippets.sh
# Intermediate output goes to $MOJO_PAPER_BUILD (default: a temp directory),
# not into the repository.
set -e
export PATH="/Applications/Isabelle2026.app/bin:$PATH"
BUILD="${MOJO_PAPER_BUILD:-${TMPDIR:-/tmp}/mojo-paper-build}"
OUT="$BUILD/isabelle"
mkdir -p "$BUILD"

# 1. LaTeX of the theories with \snip markers (Micro_Mojo_Syntax.thy).
#    Typesetting the whole session document may report LaTeX errors in
#    unrelated theories; only the generated .tex sources matter here.
rm -rf "$OUT"
isabelle build -f -d . -o document=pdf -o document_output="$OUT" Mojo_Semantics >/dev/null 2>&1 || true
sed -n '/\\snip{/,/endsnip/p' "$OUT/document/Micro_Mojo_Syntax.tex" > paper/snippets-syntax.tex

# 2. Antiquotation snippets (paper/Paper_Snippets.thy), checked against the
#    current definitions; this fails if a quoted equation no longer exists.
isabelle build -d . Mojo_Semantics
isabelle build -d . -o document_output="$OUT-paper" Mojo_Paper
sed -n '/\\snip{/,/endsnip/p' "$OUT-paper/document/Paper_Snippets.tex" > paper/snippets-interp.tex
