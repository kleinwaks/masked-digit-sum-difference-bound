import RequestProject.CarryStates
import RequestProject.Computable

/-!
# The data of the controlled-carry certificate

This file isolates the finite data of Section 4.3 ("The controlled-carry certificate") of
`masked_digit_bound.tex` — the mask of equation (33) (`eq:controlled-mask`), the fugacity of
equation (34) (`eq:controlled-x`) and the two certified constants — so that the verification
of the two large numerical facts (`RequestProject.CertDiff`, `RequestProject.CertSum`) and
their use in Theorem 1 (`RequestProject.FinalNumerics`) can refer to the same data.
-/

open scoped BigOperators
open Classical

namespace MaskedDigit

/-! ## The final data -/

/-- The largest digit `B = 26972` of equation (33) (`eq:controlled-mask`) of
`masked_digit_bound.tex`. -/
def finalB : ℕ := 26972

/-- The base `q = 27022` of equation (33) (`eq:controlled-mask`) of
`masked_digit_bound.tex`. -/
def finalQ : ℕ := 27022

/-- The six semigroup generators of equation (33) (`eq:controlled-mask`) of
`masked_digit_bound.tex`. -/
def finalGenerators : Finset ℕ := {1971, 2016, 2100, 2628, 2688, 2800}

/-- The six semigroup generators of equation (33) (`eq:controlled-mask`) of
`masked_digit_bound.tex`, as a list, for the computable enumeration of the mask. -/
def finalGeneratorsList : List ℕ := [1971, 2016, 2100, 2628, 2688, 2800]

theorem finalGenerators_coe :
    (finalGenerators : Set ℕ) = {x : ℕ | x ∈ finalGeneratorsList} := by
  ext x
  simp [finalGenerators, finalGeneratorsList]

theorem finalB_mem_closure :
    finalB ∈ AddSubmonoid.closure (finalGenerators : Set ℕ) := by
  have h1971 : (1971 : ℕ) ∈ AddSubmonoid.closure (finalGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [finalGenerators])
  have h2016 : (2016 : ℕ) ∈ AddSubmonoid.closure (finalGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [finalGenerators])
  have h2100 : (2100 : ℕ) ∈ AddSubmonoid.closure (finalGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [finalGenerators])
  have h2628 : (2628 : ℕ) ∈ AddSubmonoid.closure (finalGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [finalGenerators])
  have h2800 : (2800 : ℕ) ∈ AddSubmonoid.closure (finalGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [finalGenerators])
  have hval : finalB = 1971 + 1971 + 1971 + 1971 + 2016 + 2016 + 2100 + 2100 +
      2628 + 2628 + 2800 + 2800 := by norm_num [finalB]
  rw [hval]
  repeat' apply AddSubmonoid.add_mem
  all_goals assumption

/-- The mask data of equation (33) (`eq:controlled-mask`) of `masked_digit_bound.tex`:
`B = 26972`, `q = 27022` and `M = ⟨1971, 2016, 2100, 2628, 2688, 2800⟩ ∩ [0, B]`. -/
noncomputable def finalMaskData : MaskData where
  B := finalB
  q := finalQ
  M := generatedUpTo finalGenerators finalB
  B_pos := by norm_num [finalB]
  q_gt_B := by norm_num [finalB, finalQ]
  zero_mem := mem_generatedUpTo.2 ⟨by norm_num [finalB], zero_mem _⟩
  digits_le := by
    intro a ha
    exact (mem_generatedUpTo.1 ha).1
  B_mem := mem_generatedUpTo.2 ⟨le_refl _, finalB_mem_closure⟩

/-- The mask of the certificate is the truncated numerical semigroup of equation (33) of
`masked_digit_bound.tex`. -/
theorem finalMaskData_M : finalMaskData.M = generatedUpTo finalGenerators finalB := rfl

/-- The largest digit of the certificate's mask data. -/
theorem finalMaskData_B : finalMaskData.B = finalB := rfl

/-- The base of the certificate's mask data. -/
theorem finalMaskData_q : finalMaskData.q = finalQ := rfl

-- `finalMaskData` is sealed: its mask is a large finite set that must never be unfolded by
-- the elaborator.  All access goes through `finalMaskData_M`, `finalMaskData_B` and
-- `finalMaskData_q`.
attribute [irreducible] finalMaskData

/-- The fugacity `x = 0x1.ffde827adc0fep-1 = 4502448908984447 / 2^52` of equation (34)
(`eq:controlled-x`) of `masked_digit_bound.tex`, as an exact dyadic rational. -/
def finalX : ℚ := 4502448908984447 / 4503599627370496

/-- The certified difference-side spectral bound `ρ(T_{x,F₈}) > 582.117820` of Section 4.3
of `masked_digit_bound.tex`. -/
def cCert : ℚ := 582117820 / 1000000

/-- The certified sum-side bound `W_{8192}(x)^{1/8192} < 79.428331` of Section 4.3 of
`masked_digit_bound.tex`. -/
def pCert : ℚ := 79428331 / 1000000


end MaskedDigit
