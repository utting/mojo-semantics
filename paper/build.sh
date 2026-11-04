#!/bin/sh
# Builds paper/mojo-semantics.pdf using the tracked snippets-*.tex (no Isabelle
# run needed, only the Isabelle LaTeX style files). Run from anywhere.
set -e
cd "$(dirname "$0")"
BUILD="${MOJO_PAPER_BUILD:-${TMPDIR:-/tmp}/mojo-paper-build}"
STY="${ISABELLE_TEXINPUTS:-/Applications/Isabelle2026.app/Contents/Resources/lib/texinputs}"
mkdir -p "$BUILD/latex"
TEXINPUTS=".:$STY:" latexmk -pdf -interaction=nonstopmode -outdir="$BUILD/latex" mojo-semantics.tex >/dev/null
cp "$BUILD/latex/mojo-semantics.pdf" mojo-semantics.pdf
echo "paper/mojo-semantics.pdf ($(pdfinfo mojo-semantics.pdf | awk '/Pages/{print $2}') pages)"
