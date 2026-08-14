#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "$0")"

lake exe cache get
lake build
lake env lean AxiomAudit.lean

if grep -RInE --include='*.lean' '\b(sorry|admit)\b' RequestProject CertKernel CertKernel.lean AxiomAudit.lean; then
  echo "FAIL: unfinished proof marker found" >&2
  exit 1
fi

if grep -RInE --include='*.lean' '^[[:space:]]*(axiom|postulate)[[:space:]]' RequestProject CertKernel CertKernel.lean AxiomAudit.lean; then
  echo "FAIL: explicit project axiom or postulate found" >&2
  exit 1
fi

echo "PASS: Lean build, theorem audit, and source audit completed successfully"
