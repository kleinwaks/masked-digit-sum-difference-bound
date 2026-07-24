#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -interaction=nonstopmode -halt-on-error masked_digit_bound.tex
else
  pdflatex -interaction=nonstopmode -halt-on-error masked_digit_bound.tex
  pdflatex -interaction=nonstopmode -halt-on-error masked_digit_bound.tex
fi

printf '\nBuilt: %s\n' "$(pwd)/masked_digit_bound.pdf"
