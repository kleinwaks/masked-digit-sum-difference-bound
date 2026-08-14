# Lean formalization

This Lean 4/Mathlib project was produced with
[Aristotle (Harmonic)](https://aristotle.harmonic.fun/) and then audited
against Version 3.2 of the paper. It formalizes the structural construction,
the full finite-block theorem, both pressure passages, the
finite-state comparison lemmas, the semigroup facts, and the two final
numerical lower bounds.

## One-command verification

Install `elan`, `git`, `curl`, and `zstd`, then run:

```bash
./verify.sh
```

Run the command from this directory. The script fetches the pinned Mathlib
cache, builds all modules, elaborates `AxiomAudit.lean`, and rejects unfinished
proof markers or explicit project axioms. The first run downloads Lean 4.28.0
and Mathlib and can use substantial time, bandwidth, and disk space.

## Theorems to compare with the paper

* `MaskedDigit.MaskData.controlled_block_bound` is Proposition 3.
* `MaskedDigit.MaskData.controlled_pressure_bound` is the difference-pressure
consequence.
* `MaskedDigit.MaskData.ultimate_bound` is the two-sided pressure theorem.
* `MaskedDigit.final_controlled_carry_bound` proves
`1.19519192 < MaskedDigit.C3a`.
* `MaskedDigit.final_explicit_finite_bound` proves
`1.19102809 < MaskedDigit.C3a`.
* `MaskedDigit.Oriented.halfSign_encoding_not_injective` proves the explicit
collision for the rejected global first-half/second-half orientation.

The block-selection proof uses product-weight concentration and an even-parity
restriction, rather than the paper's fixed exact type. Its numerical proof
uses exact truncated automata with 64,003 difference states and 120,001 sum
states rather than replaying the separate C++ certificate. These are
intentional proof-implementation differences yielding the same stated
inequalities.

## Trust report

The structural theorems use only the usual Mathlib foundations reported by
`#print axioms` (`propext`, `Classical.choice`, and `Quot.sound`). The large
exact computations use `native_decide`; therefore the two final numerical
theorems additionally report `Lean.ofReduceBool` and `Lean.trustCompiler`.
This means verification trusts the Lean kernel plus Lean's native-code
evaluator for those computations.

The project contains no `sorry`, `admit`, explicit project `axiom`, or
`postulate`.

## Attribution

Aristotle asks to be credited by tagging `@Aristotle-Harmonic` on GitHub and,
when appropriate, adding:

```text
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

