import RequestProject.FinalNumerics
import RequestProject.FixedPoint

/-!
# The carry-free masked-digit example

This file formalizes Section 3 ("A carry-free masked-digit example") of
`masked_digit_bound.tex`.

Section 3 uses the numerical semigroup `H = ⟨1518, 1524, 1587, 2024, 2032, 2116⟩` of
equation (12) (`eq:record-mask`) truncated at `B = 17032`, with the carry-free base
`Q = 2B + 1 = 34065`; Proposition 2 evaluated at a single fixed fugacity certifies
equation (15) (`eq:certified`), `C₃ₐ > 1.19102809`.

The direct finite-depth certificate of Section 5, which uses the same mask data, is in
`RequestProject.FiniteDepth`.
-/

open scoped BigOperators
open Classical

namespace MaskedDigit

/-! ## The carry-free mask of Section 3 -/

/-- `B = 17032`, the truncation point of the carry-free example of Section 3 of
`masked_digit_bound.tex`. -/
def carryFreeB : ℕ := 17032

/-- `Q = 2B + 1 = 34065`, the carry-free base of Section 3 of `masked_digit_bound.tex`. -/
def carryFreeQ : ℕ := 34065

/-- The six generators of equation (12) (`eq:record-mask`) of `masked_digit_bound.tex`. -/
def carryFreeGenerators : Finset ℕ := {1518, 1524, 1587, 2024, 2032, 2116}

/-- The six generators of equation (12) (`eq:record-mask`) of `masked_digit_bound.tex`, as a
list, for the computable enumeration of the mask. -/
def carryFreeGeneratorsList : List ℕ := [1518, 1524, 1587, 2024, 2032, 2116]

theorem carryFreeGenerators_coe :
    (carryFreeGenerators : Set ℕ) = {x : ℕ | x ∈ carryFreeGeneratorsList} := by
  ext x
  simp [carryFreeGenerators, carryFreeGeneratorsList]

theorem carryFreeB_mem_closure :
    carryFreeB ∈ AddSubmonoid.closure (carryFreeGenerators : Set ℕ) := by
  have h1518 : (1518 : ℕ) ∈ AddSubmonoid.closure (carryFreeGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [carryFreeGenerators])
  have h1524 : (1524 : ℕ) ∈ AddSubmonoid.closure (carryFreeGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [carryFreeGenerators])
  have h1587 : (1587 : ℕ) ∈ AddSubmonoid.closure (carryFreeGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [carryFreeGenerators])
  have h2024 : (2024 : ℕ) ∈ AddSubmonoid.closure (carryFreeGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [carryFreeGenerators])
  have h2116 : (2116 : ℕ) ∈ AddSubmonoid.closure (carryFreeGenerators : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp [carryFreeGenerators])
  have hval : carryFreeB = 1518 + 1518 + 1518 + 1524 + 1524 + 1587 + 1587 + 2024 +
      2116 + 2116 := by norm_num [carryFreeB]
  rw [hval]
  repeat' apply AddSubmonoid.add_mem
  all_goals assumption

/-- The mask data `M = H ∩ [0, 17032]` with the carry-free base `Q = 34065` of Section 3 of
`masked_digit_bound.tex`. -/
noncomputable def carryFreeMaskData : MaskData where
  B := carryFreeB
  q := carryFreeQ
  M := generatedUpTo carryFreeGenerators carryFreeB
  B_pos := by norm_num [carryFreeB]
  q_gt_B := by norm_num [carryFreeB, carryFreeQ]
  zero_mem := mem_generatedUpTo.2 ⟨by norm_num [carryFreeB], zero_mem _⟩
  digits_le := fun a ha => (mem_generatedUpTo.1 ha).1
  B_mem := mem_generatedUpTo.2 ⟨le_refl _, carryFreeB_mem_closure⟩

theorem carryFreeMaskData_carryfree :
    carryFreeMaskData.q = 2 * carryFreeMaskData.B + 1 := by
  norm_num [carryFreeMaskData, carryFreeB, carryFreeQ]

/-- `|M| = 3121`, one of the three cardinalities of equation (13) (`eq:counts`) of
`masked_digit_bound.tex`. -/
theorem carryFree_mask_card : carryFreeMaskData.M.card = 3121 := by
  rw [show carryFreeMaskData.M = generatedUpTo carryFreeGenerators carryFreeB from rfl,
    generatedUpTo_card carryFreeGenerators_coe]
  native_decide

/-- `|M + M| = 18730`, one of the three cardinalities of equation (13) (`eq:counts`) of
`masked_digit_bound.tex`. -/
theorem carryFree_sum_card : carryFreeMaskData.sumSupport.card = 18730 := by
  rw [sumSupport_card carryFreeMaskData carryFreeGenerators_coe rfl,
    show carryFreeMaskData.B = carryFreeB from rfl]
  native_decide

/-- `|M - M| = 32369`, one of the three cardinalities of equation (13) (`eq:counts`) of
`masked_digit_bound.tex`. -/
theorem carryFree_diff_card : carryFreeMaskData.diffSupport.card = 32369 := by
  rw [diffSupport_card carryFreeMaskData carryFreeGenerators_coe rfl,
    show carryFreeMaskData.B = carryFreeB from rfl]
  native_decide

/-- `κ(1) = 14351`, the cheapest witness for difference one recorded in Section 3 of
`masked_digit_bound.tex`. -/
theorem carryFree_kappa_one : carryFreeMaskData.kappa 1 = 14351 := by
  have hmem : ∀ a : ℕ, (semiArr carryFreeGeneratorsList carryFreeB).getD a false = true →
      a ∈ carryFreeMaskData.M := by
    intro a ha
    have := (semiArr_getD_iff_mem carryFreeGeneratorsList carryFreeB a).1 ha
    exact mem_generatedUpTo.2 ⟨this.1, by rw [carryFreeGenerators_coe]; exact this.2⟩
  have h7176 : (7176 : ℕ) ∈ carryFreeMaskData.M := by
    refine hmem 7176 ?_
    native_decide
  have h7175 : (7175 : ℕ) ∈ carryFreeMaskData.M := by
    refine hmem 7175 ?_
    native_decide
  have hchk : noAdjacentBelow carryFreeGeneratorsList carryFreeMaskData.B 7176 = true := by
    rw [show carryFreeMaskData.B = carryFreeB from rfl]
    native_decide
  have := kappa_one_eq carryFreeMaskData carryFreeGenerators_coe rfl 7176 (by norm_num)
    h7176 (by norm_num; exact h7175) hchk
  omega

/-- The fixed fugacity `x₀ = e^{-λ₀}` of Section 3 of `masked_digit_bound.tex`, with
`λ₀ = 0.000321149844434550835903084464712287774157626054669874186964`. -/
noncomputable def carryFreeLambda : ℝ :=
  0.000321149844434550835903084464712287774157626054669874186964

/-! ### Certified evaluation of the two partition polynomials at `x₀ = e^{-λ₀}`

The source evaluates `P₋(x₀)` and `P₊(x₀)` in `384`-bit MPFR arithmetic with directed
rounding.  Here the same evaluation is carried out in exact fixed-point arithmetic with
`2^{-128}` granularity: `cfXlo` and `cfXhi` enclose `x₀ · 2^128`, and the arrays `fpArrLo`,
`fpArrHi` enclose all the powers `x₀^k`. -/

/-- A rational lower bound for the fugacity `x₀ = e^{-λ₀}` of Section 3 of
`masked_digit_bound.tex`, scaled by `2^128`. -/
def cfXlo : ℕ := 340173102837748742100000000000000000000

/-- A rational upper bound for the fugacity `x₀ = e^{-λ₀}` of Section 3 of
`masked_digit_bound.tex`, scaled by `2^128`. -/
def cfXhi : ℕ := 340173102837748742500000000000000000000

theorem cfX_lower : (cfXlo : ℝ) ≤ Real.exp (-carryFreeLambda) * 2 ^ 128 := by
  have hmono : Real.exp (-(0.000321149844434551 : ℝ)) ≤ Real.exp (-carryFreeLambda) :=
    Real.exp_le_exp.2 (by unfold carryFreeLambda; norm_num)
  have h := exp_neg_enclosure (t := (0.000321149844434551 : ℝ)) (by norm_num) (by norm_num)
  rw [abs_le] at h
  have hlow : (1 : ℝ) - 0.000321149844434551 + 0.000321149844434551 ^ 2 / 2 -
      0.000321149844434551 ^ 3 / 6 + 0.000321149844434551 ^ 4 / 24 -
      0.000321149844434551 ^ 5 / 100 ≤ Real.exp (-carryFreeLambda) := by
    have := h.1
    linarith [hmono]
  have hpos : (0 : ℝ) ≤ 2 ^ 128 := by positivity
  calc (cfXlo : ℝ)
      ≤ ((1 : ℝ) - 0.000321149844434551 + 0.000321149844434551 ^ 2 / 2 -
          0.000321149844434551 ^ 3 / 6 + 0.000321149844434551 ^ 4 / 24 -
          0.000321149844434551 ^ 5 / 100) * 2 ^ 128 := by
        norm_num [cfXlo]
    _ ≤ Real.exp (-carryFreeLambda) * 2 ^ 128 := mul_le_mul_of_nonneg_right hlow hpos

theorem cfX_upper : Real.exp (-carryFreeLambda) * 2 ^ 128 ≤ (cfXhi : ℝ) := by
  have hmono : Real.exp (-carryFreeLambda) ≤ Real.exp (-(0.000321149844434550 : ℝ)) :=
    Real.exp_le_exp.2 (by unfold carryFreeLambda; norm_num)
  have h := exp_neg_enclosure (t := (0.000321149844434550 : ℝ)) (by norm_num) (by norm_num)
  rw [abs_le] at h
  have hhigh : Real.exp (-carryFreeLambda) ≤
      (1 : ℝ) - 0.000321149844434550 + 0.000321149844434550 ^ 2 / 2 -
        0.000321149844434550 ^ 3 / 6 + 0.000321149844434550 ^ 4 / 24 +
        0.000321149844434550 ^ 5 / 100 := by
    have := h.2
    linarith [hmono]
  have hpos : (0 : ℝ) ≤ 2 ^ 128 := by positivity
  calc Real.exp (-carryFreeLambda) * 2 ^ 128
      ≤ ((1 : ℝ) - 0.000321149844434550 + 0.000321149844434550 ^ 2 / 2 -
          0.000321149844434550 ^ 3 / 6 + 0.000321149844434550 ^ 4 / 24 +
          0.000321149844434550 ^ 5 / 100) * 2 ^ 128 :=
        mul_le_mul_of_nonneg_right hhigh hpos
    _ ≤ (cfXhi : ℝ) := by norm_num [cfXhi]

/-- The fixed-point value of `P₋(x₀) · 2^128`, rounded downwards throughout. -/
def cfPmSum : ℕ :=
  sumMapFold (diffCostList carryFreeGeneratorsList carryFreeB) fun c =>
      (fpArrLo cfXlo 128 (2 * carryFreeB)).getD c 0

/-- The fixed-point value of `P₊(x₀) · 2^128`, rounded upwards throughout. -/
def cfPpSum : ℕ :=
  sumMapFold (semiSumList carryFreeGeneratorsList carryFreeB) fun s =>
      (fpArrHi cfXhi 128 (2 * carryFreeB)).getD s 0

/-- Every difference digit of the carry-free mask has an explicit witness pair in the mask. -/
theorem cfDiffCostOK : diffCostOK carryFreeGeneratorsList carryFreeB = true := by native_decide

theorem cfPmSum_ge : 66832473254 * 2 ^ 128 ≤ cfPmSum * 10 ^ 8 := by native_decide

theorem cfPpSum_le : cfPpSum * 10 ^ 9 ≤ 91030993706 * 2 ^ 128 := by native_decide

theorem carryFree_x_le_one : Real.exp (-carryFreeLambda) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  unfold carryFreeLambda; norm_num

/-- **A certified lower bound for `P₋(x₀)`** in Section 3 of `masked_digit_bound.tex`. -/
theorem carryFree_Pminus_lower :
    (66832473254 / 10 ^ 8 : ℝ) ≤ carryFreeMaskData.Pminus (Real.exp (-carryFreeLambda)) := by
  have hx0 : (0 : ℝ) ≤ Real.exp (-carryFreeLambda) := (Real.exp_pos _).le
  have hB : carryFreeMaskData.B = carryFreeB := rfl
  have hcost := costSum_le_Pminus carryFreeMaskData carryFreeGenerators_coe rfl hx0
    carryFree_x_le_one (by rw [hB]; exact cfDiffCostOK)
  rw [hB] at hcost
  have hfp := sum_pow_ge (diffCostList carryFreeGeneratorsList carryFreeB) cfXlo 128
    (2 * carryFreeB) (Real.exp (-carryFreeLambda)) hx0 cfX_lower (diffCostList_le cfDiffCostOK)
  have hcast : (66832473254 : ℝ) * 2 ^ 128 ≤
      (((diffCostList carryFreeGeneratorsList carryFreeB).map fun c =>
        (fpArrLo cfXlo 128 (2 * carryFreeB)).getD c 0).sum : ℕ) * 10 ^ 8 := by
    have := cfPmSum_ge
    rw [cfPmSum, sumMapFold_eq] at this
    exact_mod_cast this
  have hpow : (0 : ℝ) < 2 ^ 128 := by positivity
  have hstep : (66832473254 / 10 ^ 8 : ℝ) ≤
      ((((diffCostList carryFreeGeneratorsList carryFreeB).map fun c =>
        (fpArrLo cfXlo 128 (2 * carryFreeB)).getD c 0).sum : ℕ) : ℝ) / 2 ^ 128 := by
    rw [le_div_iff₀ hpow]
    linarith
  have hsum : ((((diffCostList carryFreeGeneratorsList carryFreeB).map fun c =>
        (fpArrLo cfXlo 128 (2 * carryFreeB)).getD c 0).sum : ℕ) : ℝ) / 2 ^ 128 ≤
      ((diffCostList carryFreeGeneratorsList carryFreeB).map fun c =>
        Real.exp (-carryFreeLambda) ^ c).sum := by
    rw [div_le_iff₀ hpow]
    exact hfp
  linarith [hcost]

/-- **A certified upper bound for `P₊(x₀)`** in Section 3 of `masked_digit_bound.tex`. -/
theorem carryFree_Pplus_upper :
    carryFreeMaskData.Pplus (Real.exp (-carryFreeLambda)) ≤ (91030993706 / 10 ^ 9 : ℝ) := by
  have hx0 : (0 : ℝ) ≤ Real.exp (-carryFreeLambda) := (Real.exp_pos _).le
  have hB : carryFreeMaskData.B = carryFreeB := rfl
  have hP := Pplus_eq_sumList carryFreeMaskData carryFreeGenerators_coe rfl
    (Real.exp (-carryFreeLambda))
  rw [hB] at hP
  have hfp := sum_pow_le (semiSumList carryFreeGeneratorsList carryFreeB) cfXhi 128
    (2 * carryFreeB) (Real.exp (-carryFreeLambda)) hx0 cfX_upper semiSumList_le
  have hcast : (((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
        (fpArrHi cfXhi 128 (2 * carryFreeB)).getD s 0).sum : ℕ) * 10 ^ 9 ≤
      (91030993706 : ℝ) * 2 ^ 128 := by
    have := cfPpSum_le
    rw [cfPpSum, sumMapFold_eq] at this
    exact_mod_cast this
  have hpow : (0 : ℝ) < 2 ^ 128 := by positivity
  have hstep : ((((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
        (fpArrHi cfXhi 128 (2 * carryFreeB)).getD s 0).sum : ℕ) : ℝ) / 2 ^ 128 ≤
      (91030993706 / 10 ^ 9 : ℝ) := by
    rw [div_le_iff₀ hpow]
    linarith
  have hsum : ((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
      Real.exp (-carryFreeLambda) ^ s).sum ≤
      ((((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
        (fpArrHi cfXhi 128 (2 * carryFreeB)).getD s 0).sum : ℕ) : ℝ) / 2 ^ 128 := by
    rw [le_div_iff₀ hpow]
    exact hfp
  rw [hP]
  linarith

/-- The certified partition-sum comparison of Section 3 of `masked_digit_bound.tex`, proved
there with `384`-bit MPFR arithmetic and directed rounding.  Here it is proved by exact
fixed-point arithmetic (`carryFree_Pminus_lower`, `carryFree_Pplus_upper`) combined with the
certified logarithm comparison `carryFree_exponent_comparison`. -/
theorem carryFree_partition_certificate :
    (1.19102809 : ℝ) <
      1 + (Real.log (carryFreeMaskData.Pminus (Real.exp (-carryFreeLambda))) -
            Real.log (carryFreeMaskData.Pplus (Real.exp (-carryFreeLambda)))) /
          Real.log carryFreeMaskData.q := by
  have hx0 : (0 : ℝ) < Real.exp (-carryFreeLambda) := Real.exp_pos _
  have hPm := carryFree_Pminus_lower
  have hPp := carryFree_Pplus_upper
  have hPp0 : 0 < carryFreeMaskData.Pplus (Real.exp (-carryFreeLambda)) :=
    carryFreeMaskData.Pplus_pos hx0
  have hPm0 : 0 < carryFreeMaskData.Pminus (Real.exp (-carryFreeLambda)) :=
    carryFreeMaskData.Pminus_pos hx0
  -- logarithms of the two certified rational bounds
  have hlogm : Real.log (66832473254 / 10 ^ 8 : ℝ) ≤
      Real.log (carryFreeMaskData.Pminus (Real.exp (-carryFreeLambda))) :=
    Real.log_le_log (by norm_num) hPm
  have hlogp : Real.log (carryFreeMaskData.Pplus (Real.exp (-carryFreeLambda))) ≤
      Real.log (91030993706 / 10 ^ 9 : ℝ) := Real.log_le_log hPp0 hPp
  have hratio : Real.log ((7341727 : ℝ) / 1000000) ≤
      Real.log (66832473254 / 10 ^ 8 : ℝ) - Real.log (91030993706 / 10 ^ 9 : ℝ) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    apply Real.log_le_log (by norm_num)
    norm_num
  have hcomp := carryFree_exponent_comparison
  have hq : (carryFreeMaskData.q : ℝ) = 34065 := by norm_num [carryFreeMaskData, carryFreeQ]
  have hlogq : 0 < Real.log 34065 := Real.log_pos (by norm_num)
  rw [hq]
  have hnum : (0.19102809 : ℝ) * Real.log 34065 <
      Real.log (carryFreeMaskData.Pminus (Real.exp (-carryFreeLambda))) -
        Real.log (carryFreeMaskData.Pplus (Real.exp (-carryFreeLambda))) := by
    linarith
  have hdiv : (0.19102809 : ℝ) <
      (Real.log (carryFreeMaskData.Pminus (Real.exp (-carryFreeLambda))) -
        Real.log (carryFreeMaskData.Pplus (Real.exp (-carryFreeLambda)))) / Real.log 34065 :=
    (lt_div_iff₀ hlogq).2 (by linarith)
  linarith

/-- **Equation (15) (`eq:certified`) of `masked_digit_bound.tex`:** the carry-free limiting
certificate `C₃ₐ > 1.19102809`, obtained from Proposition 2 at the single fixed value
`λ₀`. -/
theorem carryFree_certified : (1.19102809 : ℝ) < C3a := by
  have hx0 : (0 : ℝ) < Real.exp (-carryFreeLambda) := Real.exp_pos _
  have hlam : (0 : ℝ) < carryFreeLambda := by
    unfold carryFreeLambda; norm_num
  have hx1 : Real.exp (-carryFreeLambda) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  exact lt_of_lt_of_le carryFree_partition_certificate
    (carryFreeMaskData.masked_digit_bound carryFreeMaskData_carryfree _ hx0 hx1)

end MaskedDigit
