import RequestProject.GHRConstant
import RequestProject.ProductWeights
import RequestProject.MaskData
import RequestProject.CoreConstruction
import RequestProject.OrientedBlocks
import RequestProject.OrientedHalfSplit
import RequestProject.MaskedCarryFree
import RequestProject.Balancing
import RequestProject.ControlledDifference
import RequestProject.ControlledSum
import RequestProject.CarryStates
import RequestProject.Computable
import RequestProject.FixedPoint
import RequestProject.LogBounds
import RequestProject.LogNumerics
import RequestProject.StirlingBounds
import RequestProject.TypeCount
import RequestProject.FiniteTypeWords
import RequestProject.FinalNumerics
import RequestProject.FiniteCertificate
import RequestProject.FiniteDepth
import RequestProject.SemigroupStructure

/-!
# Improved lower bound for the Gyarmati--Hennecart--Ruzsa sum-difference constant using masked digits and controlled carries

This is the top-level file of the formalization of `masked_digit_bound.tex`.  It imports the
whole development:

* `GHRDigits`     — the base-`q` digit construction of [GHR2007] behind the finite-set
  principle (1);
* `GHRConstant`   — Section 1: the constant `C₃ₐ`, the finite-set principle (1) and the
  dilation argument giving (2);
* `ProductWeights` — the discrete concentration input replacing the method of types;
* `MaskData`      — the mask, the minimum witness cost `κ` (3) and the partition
  polynomials (4);
* `CoreConstruction` — the digit construction common to Propositions 2, 3 and 5;
* `OrientedBlocks`  — the positional orientation of the (unique, nonzero) self-inverse
  residue `q^k/2`, used to keep *every* residue contribution in `Z_k(x)` in Proposition 3;
* `OrientedHalfSplit` — why those occurrences are paired off rather than split into a prefix
  and a suffix: the literal first-half/second-half rule breaks the injectivity of the
  encoding, as an explicit collision shows;
* `MaskedCarryFree` — Section 2: Proposition 2 and the Remark on Zheng's optimization;
* `Balancing`     — Section 2: the Remark "The balancing condition at an interior optimum";
* `ControlledDifference` — Section 4: the block costs (16), `Z_k` (17), Proposition 3 and
  Lemma 4;
* `ControlledSum` — Section 4.1: `W_ℓ`, the sum pressure and Proposition 5;
* `CarryStates`   — Section 4.2: the carry-state transfer operator and Proposition 6;
* `Computable`    — the verified enumeration of the truncated numerical semigroups used as
  masks in Sections 3 and 4.3, and of their sum and difference supports;
* `FixedPoint`, `LogBounds`, `LogNumerics`, `StirlingBounds` — the certified arithmetic
  (directed fixed-point evaluation of the partition polynomials, Mercator enclosures of
  logarithms, effective two-sided Stirling bounds) behind the numerical comparisons of
  Sections 3, 4.3 and 5;
* `TypeCount`, `FiniteTypeWords` — the method-of-types counting of signed difference words
  with a prescribed symmetric type, used in Section 5;
* `FinalNumerics` — Section 4.3: the controlled-carry certificate `C₃ₐ > 1.19519192`;
* `FiniteCertificate` — Section 3: the carry-free example, certifying `C₃ₐ > 1.19102809`;
* `FiniteDepth` — Section 5: the explicit finite-depth certificate, certifying
  `C₃ₐ > 1.19102809` with no asymptotic input;
* `SemigroupStructure` — Section 6: the simple-gluing description of the column semigroup,
  the `2 × 3` generator grid, the exact and near relations it carries, and the resulting
  bounds on the minimum witness cost.

## Status

Everything in the development is proved from first principles; the file contains no
assumptions beyond the axioms of Lean and `Mathlib`.

In particular:

* the Gyarmati--Hennecart--Ruzsa finite-set principle, equation (1), which the source quotes
  from [GHR2007], is *proved* here (`ghr_finite_set_lower_bound` in `GHRConstant`, from the
  digit construction of `GHRDigits`);
* the two large computations of Section 4.3 are *verified* here: the certificate kernel
  `CertKernel.Basic` (integer fixed-point arithmetic, evaluated by `native_decide`) checks a
  Collatz--Wielandt positive vector on each side of a truncated carry automaton, and
  `CertDiff`, `CertSum` turn those two checks into `final_difference_certificate`
  (`log 582.117820 ≤ 𝒫₋(x)`) and `final_sum_certificate` (`𝒫₊(x) ≤ log 79.428331`).

Consequently all of Theorem 1 is unconditional: the carry-free certificate of Section 3
(`carryFree_certified`) and the finite-depth certificate of Section 5
(`final_explicit_finite_bound`), both giving `C₃ₐ > 1.19102809`, and the controlled-carry
certificate of Section 4.3 (`final_controlled_carry_bound`), giving `C₃ₐ > 1.19519192`.

The controlled-carry block bound of Section 4 (`controlled_block_bound`) is the exact
statement of Proposition 3: it bounds `1 + (k⁻¹ log Z_k(x) - log P₊(x)) / log q` by `C₃ₐ`,
with the full block partition sum `Z_k(x)`.  No residue class is discarded: the unique
nonzero residue `h` with `h = -h (mod q^k)`, namely `h = q^k/2`, is kept by prescribing an
even number of its occurrences and orienting them deterministically from their positions in
the residue word (`OrientedBlocks`), so that its two orientations have equal residue and
equal cost and their contributions to the two digit budgets cancel exactly.

Independently of the finite-set principle, `GHRConstant` also proves that the supremum
defining `C₃ₐ` is a genuine real number: `1 ≤ C₃ₐ ≤ 3/2`.
-/
