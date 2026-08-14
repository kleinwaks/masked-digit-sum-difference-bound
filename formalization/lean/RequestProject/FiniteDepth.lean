import RequestProject.FiniteTypeWords
import RequestProject.FiniteCertificate
import RequestProject.StirlingBounds
import RequestProject.LogNumerics

/-!
# The direct finite-depth certificate

This file formalizes Section 5 ("A direct finite-depth certificate") of
`masked_digit_bound.tex`: the carry-free mask of Section 3 is used with an explicitly
specified finite set `U` of base-`Q` integers with `N = 10¹³` digits, and the bound
`C₃ₐ > 1.19102809` (equation (36), `eq:finite-certified`) is derived from it with no
asymptotic input at all.
-/

open scoped BigOperators
open Classical

namespace MaskedDigit

/-! ## The direct finite-depth certificate of Section 5 -/

/-- The fugacity `x_f = 0.9996789017186568` of Section 5 of `masked_digit_bound.tex`. -/
def xfRat : ℚ := 9996789017186568 / 10 ^ 16

/-- The construction depth `N = 10¹³` of Section 5 of `masked_digit_bound.tex`. -/
def Nfin : ℕ := 10 ^ 13

/-- `W = ∑_{d ∈ D} x_f^{κ(d)} = P₋(x_f)`, the normalizing partition sum of Section 5 of
`masked_digit_bound.tex`. -/
noncomputable def Wfin : ℝ := carryFreeMaskData.Pminus (xfRat : ℝ)

/-- The positive part of the difference support, over which the symmetric type counts of
Section 5 of `masked_digit_bound.tex` are indexed. -/
noncomputable def posDiff : Finset ℤ := carryFreeMaskData.diffSupport.filter fun d => 0 < d

/-- The type counts `n_d = ⌊N x_f^{κ(d)} / W⌋` for `d > 0` of Section 5 of
`masked_digit_bound.tex`; the counts for `d < 0` are equal by symmetry. -/
noncomputable def nCount (d : ℤ) : ℕ :=
  ⌊(Nfin : ℝ) * (xfRat : ℝ) ^ carryFreeMaskData.kappa d / Wfin⌋₊

/-- The zero-digit count `n₀ = N - 2 ∑_{d > 0} n_d` of Section 5 of
`masked_digit_bound.tex`. -/
noncomputable def n0Count : ℕ := Nfin - 2 * ∑ d ∈ posDiff, nCount d

/-- The digit budget `L = ½ ∑_{d ∈ D} n_d κ(d) = ∑_{d > 0} n_d κ(d)` of Section 5 of
`masked_digit_bound.tex`. -/
noncomputable def Lfin : ℕ := ∑ d ∈ posDiff, nCount d * carryFreeMaskData.kappa d

/-- The explicit finite set `U = {∑_{i<N} aᵢ Qⁱ : aᵢ ∈ M, ∑ aᵢ ≤ L}` of Section 5 of
`masked_digit_bound.tex`.  It is specified symbolically and is never enumerated. -/
noncomputable def Ufin : Finset ℕ := carryFreeMaskData.maskSet Nfin Lfin

theorem Ufin_eq : Ufin = carryFreeMaskData.maskSet Nfin Lfin := rfl

/-- The symmetric type `(n_d)_{d ∈ D}` of Section 5 of `masked_digit_bound.tex`: the counts
`n_d = ⌊N x_f^{κ(d)} / W⌋` for `d > 0`, extended by `n_{-d} = n_d` and by the zero-digit count
`n₀` at `d = 0`. -/
noncomputable def ncType (d : ℤ) : ℕ := if d = 0 then n0Count else nCount |d|

/-- The multinomial count `D_N = N! / (n₀! ∏_{d>0} (n_d!)²)` of signed difference words with
the prescribed symmetric type, from Section 5 of `masked_digit_bound.tex`.  It is written here
as the multinomial coefficient `(∑_{d ∈ D} n_d)! / ∏_{d ∈ D} n_d!` of the full symmetric type;
`DNfin_eq` identifies it with the expression displayed in the source. -/
noncomputable def DNfin : ℕ :=
  Nat.factorial (∑ d ∈ carryFreeMaskData.diffSupport, ncType d) /
    ∏ d ∈ carryFreeMaskData.diffSupport, Nat.factorial (ncType d)

/-! ### Certified evaluation of the type counts of Section 5

Section 5 of `masked_digit_bound.tex` fixes the fugacity `x_f = 0.9996789017186568`, sets
`W = P₋(x_f)` and defines the symmetric type by `n_d = ⌊N x_f^{κ(d)} / W⌋` for `d > 0`.  The
source evaluates these `16184` floors in `512`-bit MPFR arithmetic with directed rounding.
Here the same evaluation is carried out in exact `2^{-128}` fixed-point arithmetic: `xfLo` and
`xfHi` enclose `x_f · 2^128`, the arrays `cfAlo` and `cfAhi` enclose all the powers
`x_f^k · 2^128`, `cfWlo` and `cfWhi` enclose `W · 2^128`, and the computable check
`cfFloorOK` verifies that the resulting lower and upper evaluations of every floor agree, so
that each `n_d` is determined. -/

/-- A lower fixed-point bound for the fugacity `x_f` of Section 5 of
`masked_digit_bound.tex`, scaled by `2^128`. -/
def xfLo : ℕ := 9996789017186568 * 2 ^ 128 / 10 ^ 16

/-- An upper fixed-point bound for the fugacity `x_f` of Section 5 of
`masked_digit_bound.tex`, scaled by `2^128`. -/
def xfHi : ℕ := (9996789017186568 * 2 ^ 128 + 10 ^ 16 - 1) / 10 ^ 16

/-- Downward-rounded fixed-point powers `x_f^k · 2^128` for `k ≤ 2B`. -/
def cfAlo : Array ℕ := fpArrLo xfLo 128 (2 * carryFreeB)

/-- Upward-rounded fixed-point powers `x_f^k · 2^128` for `k ≤ 2B`. -/
def cfAhi : Array ℕ := fpArrHi xfHi 128 (2 * carryFreeB)

/-- A lower fixed-point bound for the normalizing sum `W = P₋(x_f)` of Section 5 of
`masked_digit_bound.tex`, scaled by `2^128`. -/
def cfWlo : ℕ :=
  sumMapFold (diffCostList carryFreeGeneratorsList carryFreeB) fun c => cfAlo.getD c 0

/-- An upper fixed-point bound for the normalizing sum `W = P₋(x_f)` of Section 5 of
`masked_digit_bound.tex`, scaled by `2^128`. -/
def cfWhi : ℕ :=
  sumMapFold (diffCostList carryFreeGeneratorsList carryFreeB) fun c => cfAhi.getD c 0

/-- The indices `i` of the strictly positive differences `d = i − B` of the difference
support, over which the type counts of Section 5 of `masked_digit_bound.tex` are indexed. -/
def cfPosIdxList : List ℕ :=
  (diffIdxList carryFreeGeneratorsList carryFreeB).filter fun i => carryFreeB < i

/-- The witness cost `κ(i − B)` of the difference `d = i − B`. -/
def cfCostAt (i : ℕ) : ℕ :=
  let a := diffWitnessAt (semiArr carryFreeGeneratorsList carryFreeB)
    (semiMask carryFreeGeneratorsList carryFreeB) carryFreeB i
  a + (a + carryFreeB - i)

/-- The list of witness costs `κ(d)` for the strictly positive differences `d`, computed with
the semigroup table shared across the whole scan. -/
def cfPosCostList : List ℕ :=
  let t := semiArr carryFreeGeneratorsList carryFreeB
  let ml := semiMask carryFreeGeneratorsList carryFreeB
  cfPosIdxList.map fun i =>
    let a := diffWitnessAt t ml carryFreeB i
    a + (a + carryFreeB - i)

theorem cfPosCostList_eq : cfPosCostList = cfPosIdxList.map cfCostAt := rfl

/-- The fixed-point evaluation of the type count `n_d = ⌊N x_f^{κ(d)} / W⌋` of Section 5 of
`masked_digit_bound.tex`, rounded downwards throughout. -/
def cfCountAt (c : ℕ) : ℕ := Nfin * cfAlo.getD c 0 / cfWhi

/-- The fixed-point evaluation of `∑_{d > 0} n_d`. -/
def cfNSum : ℕ := sumMapFold cfPosCostList cfCountAt

/-- The fixed-point evaluation of `L = ∑_{d > 0} n_d κ(d)`. -/
def cfLSum : ℕ := sumMapFold cfPosCostList fun c => cfCountAt c * c

/-- The computable check that the downward- and the upward-rounded evaluation of every one of
the `16184` floors of Section 5 of `masked_digit_bound.tex` agree, so that every type count is
determined by the fixed-point computation. -/
def cfFloorOK : Bool :=
  cfPosCostList.all fun c => cfCountAt c == Nfin * cfAhi.getD c 0 / cfWlo

theorem cfWlo_pos : 0 < cfWlo := by native_decide

theorem cfFloorOK_true : cfFloorOK = true := by native_decide

theorem cfNSum_value : cfNSum = 4992518598801 := by native_decide

theorem cfLSum_value : cfLSum = 51500691976683641 := by native_decide

theorem xfRat_nonneg : (0 : ℝ) ≤ (xfRat : ℝ) := by norm_num [xfRat]

theorem xfLo_le : (xfLo : ℝ) ≤ (xfRat : ℝ) * 2 ^ 128 := by
  have h : ((9996789017186568 * 2 ^ 128 / 10 ^ 16 : ℕ) : ℝ) ≤
      ((9996789017186568 * 2 ^ 128 : ℕ) : ℝ) / ((10 ^ 16 : ℕ) : ℝ) := Nat.cast_div_le
  have hx : (xfRat : ℝ) = 9996789017186568 / 10 ^ 16 := by
    rw [xfRat]; push_cast; ring
  rw [hx, xfLo]
  push_cast at h ⊢
  linarith

theorem xfHi_ge : (xfRat : ℝ) * 2 ^ 128 ≤ (xfHi : ℝ) := by
  have h := ceil_div_ge (9996789017186568 * 2 ^ 128) (10 ^ 16) (by norm_num)
  have hx : (xfRat : ℝ) = 9996789017186568 / 10 ^ 16 := by
    rw [xfRat]; push_cast; ring
  rw [hx, xfHi]
  push_cast at h ⊢
  linarith

/-- `W = P₋(x_f)` written as the explicit sum over the enumerated witness costs. -/
theorem Wfin_eq_costSum :
    Wfin = ((diffCostList carryFreeGeneratorsList carryFreeB).map
      fun c => (xfRat : ℝ) ^ c).sum :=
  Pminus_eq_costSum carryFreeMaskData carryFreeGenerators_coe rfl cfDiffCostOK _

theorem cfWlo_le : (cfWlo : ℝ) ≤ Wfin * 2 ^ 128 := by
  rw [Wfin_eq_costSum]
  simp only [cfWlo, cfAlo, sumMapFold_eq]
  exact sum_pow_ge _ xfLo 128 (2 * carryFreeB) _ xfRat_nonneg xfLo_le
    (diffCostList_le cfDiffCostOK)

theorem cfWhi_ge : Wfin * 2 ^ 128 ≤ (cfWhi : ℝ) := by
  rw [Wfin_eq_costSum]
  simp only [cfWhi, cfAhi, sumMapFold_eq]
  exact sum_pow_le _ xfHi 128 (2 * carryFreeB) _ xfRat_nonneg xfHi_ge
    (diffCostList_le cfDiffCostOK)

theorem Wfin_pos : 0 < Wfin := by
  have h1 : (0 : ℝ) < (cfWlo : ℝ) := by exact_mod_cast cfWlo_pos
  have h2 := cfWlo_le
  nlinarith

theorem cfWhi_pos_real : (0 : ℝ) < (cfWhi : ℝ) := by
  have := cfWhi_ge
  nlinarith [Wfin_pos]

theorem cfWlo_pos_real : (0 : ℝ) < (cfWlo : ℝ) := by exact_mod_cast cfWlo_pos

theorem cfPosIdxList_subset {i : ℕ} (hi : i ∈ cfPosIdxList) :
    i ∈ diffIdxList carryFreeGeneratorsList carryFreeB := (List.mem_filter.1 hi).1

/-- The witness cost of the difference `d = i − B` is the minimum witness cost `κ(d)` of
equation (3) of `masked_digit_bound.tex`. -/
theorem cfKappa_eq {i : ℕ} (hi : i ∈ cfPosIdxList) :
    carryFreeMaskData.kappa ((i : ℤ) - (carryFreeB : ℤ)) = cfCostAt i :=
  kappa_eq_diffCost carryFreeMaskData carryFreeGenerators_coe rfl cfDiffCostOK
    (cfPosIdxList_subset hi)

/-- **The type counts of Section 5 of `masked_digit_bound.tex` are exactly the values computed
in fixed point**: the downward- and upward-rounded evaluations of the floor agree. -/
theorem nCount_eq {i : ℕ} (hi : i ∈ cfPosIdxList) :
    nCount ((i : ℤ) - (carryFreeB : ℤ)) = cfCountAt (cfCostAt i) := by
  have hidx := cfPosIdxList_subset hi
  have hcmem : cfCostAt i ∈ diffCostList carryFreeGeneratorsList carryFreeB :=
    List.mem_map_of_mem hidx
  have hcost : cfCostAt i ∈ cfPosCostList := by
    rw [cfPosCostList_eq]; exact List.mem_map_of_mem hi
  set c := cfCostAt i with hc
  have hcle : c ≤ 2 * carryFreeB := diffCostList_le cfDiffCostOK c hcmem
  have hAlo : ((cfAlo.getD c 0 : ℕ) : ℝ) ≤ (xfRat : ℝ) ^ c * 2 ^ 128 :=
    fpArrLo_le xfLo 128 (2 * carryFreeB) _ xfRat_nonneg xfLo_le c hcle
  have hAhi : (xfRat : ℝ) ^ c * 2 ^ 128 ≤ ((cfAhi.getD c 0 : ℕ) : ℝ) :=
    fpArrHi_ge xfHi 128 (2 * carryFreeB) _ xfRat_nonneg xfHi_ge c hcle
  have hN : (0 : ℝ) ≤ (Nfin : ℝ) := Nat.cast_nonneg _
  have hpc : (0 : ℝ) ≤ (xfRat : ℝ) ^ c := pow_nonneg xfRat_nonneg c
  have hlow : ((Nfin * cfAlo.getD c 0 : ℕ) : ℝ) / ((cfWhi : ℕ) : ℝ)
      ≤ (Nfin : ℝ) * (xfRat : ℝ) ^ c / Wfin := by
    rw [div_le_div_iff₀ cfWhi_pos_real Wfin_pos]
    push_cast
    calc (Nfin : ℝ) * ((cfAlo.getD c 0 : ℕ) : ℝ) * Wfin
        = (Nfin : ℝ) * (((cfAlo.getD c 0 : ℕ) : ℝ) * Wfin) := by ring
      _ ≤ (Nfin : ℝ) * (((xfRat : ℝ) ^ c * 2 ^ 128) * Wfin) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAlo Wfin_pos.le) hN
      _ = (Nfin : ℝ) * ((xfRat : ℝ) ^ c * (Wfin * 2 ^ 128)) := by ring
      _ ≤ (Nfin : ℝ) * ((xfRat : ℝ) ^ c * (cfWhi : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cfWhi_ge hpc) hN
      _ = (Nfin : ℝ) * (xfRat : ℝ) ^ c * (cfWhi : ℝ) := by ring
  have hhigh : (Nfin : ℝ) * (xfRat : ℝ) ^ c / Wfin
      ≤ ((Nfin * cfAhi.getD c 0 : ℕ) : ℝ) / ((cfWlo : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ Wfin_pos cfWlo_pos_real]
    push_cast
    calc (Nfin : ℝ) * (xfRat : ℝ) ^ c * (cfWlo : ℝ)
        = (Nfin : ℝ) * ((xfRat : ℝ) ^ c * (cfWlo : ℝ)) := by ring
      _ ≤ (Nfin : ℝ) * ((xfRat : ℝ) ^ c * (Wfin * 2 ^ 128)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left cfWlo_le hpc) hN
      _ = (Nfin : ℝ) * (((xfRat : ℝ) ^ c * 2 ^ 128) * Wfin) := by ring
      _ ≤ (Nfin : ℝ) * (((cfAhi.getD c 0 : ℕ) : ℝ) * Wfin) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAhi Wfin_pos.le) hN
      _ = (Nfin : ℝ) * ((cfAhi.getD c 0 : ℕ) : ℝ) * Wfin := by ring
  have hfl : cfCountAt c ≤ ⌊(Nfin : ℝ) * (xfRat : ℝ) ^ c / Wfin⌋₊ := by
    refine Nat.le_floor (le_trans ?_ hlow)
    rw [cfCountAt]
    exact_mod_cast Nat.cast_div_le
  have hfu : ⌊(Nfin : ℝ) * (xfRat : ℝ) ^ c / Wfin⌋₊ ≤ Nfin * cfAhi.getD c 0 / cfWlo := by
    have h := Nat.floor_mono hhigh
    rwa [Nat.floor_div_eq_div (K := ℝ)] at h
  have heq : cfCountAt c = Nfin * cfAhi.getD c 0 / cfWlo := by
    have h := List.all_eq_true.1 cfFloorOK_true c hcost
    simpa using h
  have hkap : carryFreeMaskData.kappa ((i : ℤ) - (carryFreeB : ℤ)) = c := cfKappa_eq hi
  unfold nCount
  rw [hkap]
  omega

theorem cfPosIdxList_nodup : cfPosIdxList.Nodup :=
  ((List.nodup_range).filter _).filter _

/-- The positive part of the difference support of Section 5 of `masked_digit_bound.tex`,
enumerated by `cfPosIdxList`. -/
theorem posDiff_eq :
    posDiff = (cfPosIdxList.map fun i : ℕ => (i : ℤ) - (carryFreeB : ℤ)).toFinset := by
  have hds : carryFreeMaskData.diffSupport =
      (semiDiffList carryFreeGeneratorsList carryFreeB).toFinset :=
    diffSupport_eq carryFreeMaskData carryFreeGenerators_coe rfl
  ext d
  simp only [posDiff, hds, Finset.mem_filter, List.mem_toFinset, semiDiffList, List.mem_map,
    cfPosIdxList, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hpos⟩
    exact ⟨i, ⟨hi, by omega⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hlt⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, by omega⟩

theorem posDiff_sum (g : ℤ → ℕ) :
    ∑ d ∈ posDiff, g d =
      (cfPosIdxList.map fun i : ℕ => g ((i : ℤ) - (carryFreeB : ℤ))).sum := by
  have hinj : Function.Injective fun i : ℕ => (i : ℤ) - (carryFreeB : ℤ) := by
    intro a b hab
    simp only at hab
    have : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast this
  rw [posDiff_eq, List.sum_toFinset _ (cfPosIdxList_nodup.map hinj), List.map_map,
    Function.comp_def]

theorem posDiff_nCount_sum : ∑ d ∈ posDiff, nCount d = cfNSum := by
  have hmap : (cfPosIdxList.map fun i : ℕ => nCount ((i : ℤ) - (carryFreeB : ℤ)))
      = cfPosIdxList.map fun i => cfCountAt (cfCostAt i) :=
    List.map_congr_left fun i hi => nCount_eq hi
  rw [posDiff_sum, hmap, cfNSum, sumMapFold_eq, cfPosCostList_eq, List.map_map,
    Function.comp_def]

theorem posDiff_Lfin_sum : Lfin = cfLSum := by
  have hmap : (cfPosIdxList.map fun i : ℕ =>
        nCount ((i : ℤ) - (carryFreeB : ℤ)) *
          carryFreeMaskData.kappa ((i : ℤ) - (carryFreeB : ℤ)))
      = cfPosIdxList.map fun i => cfCountAt (cfCostAt i) * cfCostAt i := by
    refine List.map_congr_left fun i hi => ?_
    rw [nCount_eq hi, cfKappa_eq hi]
  rw [Lfin, posDiff_sum (fun d => nCount d * carryFreeMaskData.kappa d), hmap, cfLSum,
    sumMapFold_eq, cfPosCostList_eq, List.map_map, Function.comp_def]


/-- `n₀ = 14962802398`, the exact zero-digit count certified in Section 5 of
`masked_digit_bound.tex`. -/
theorem n0Count_value : n0Count = 14962802398 := by
  rw [n0Count, posDiff_nCount_sum, cfNSum_value]
  norm_num [Nfin]

/-- `L = 51500691976683641`, the exact digit budget certified in Section 5 of
`masked_digit_bound.tex`. -/
theorem Lfin_value : Lfin = 51500691976683641 := by
  rw [posDiff_Lfin_sum, cfLSum_value]

set_option maxRecDepth 100000

theorem ncType_neg (d : ℤ) : ncType (-d) = ncType d := by
  simp [ncType, neg_eq_zero, abs_neg]

theorem ncType_zero : ncType 0 = n0Count := by simp [ncType]

theorem ncType_of_pos {d : ℤ} (hd : 0 < d) : ncType d = nCount d := by
  simp [ncType, ne_of_gt hd, abs_of_pos hd]

theorem posDiff_filter : carryFreeMaskData.diffSupport.filter (fun d => 0 < d) = posDiff := by
  rw [posDiff]

theorem two_nCount_sum_le : 2 * ∑ d ∈ posDiff, nCount d ≤ Nfin := by
  rw [posDiff_nCount_sum, cfNSum_value]
  norm_num [Nfin]

/-- The type counts of Section 5 of `masked_digit_bound.tex` add up to the depth `N`:
`n₀ + 2 ∑_{d>0} n_d = N`. -/
theorem ncType_sum : ∑ d ∈ carryFreeMaskData.diffSupport, ncType d = Nfin := by
  rw [carryFreeMaskData.sum_diffSupport_symm ncType, posDiff_filter, ncType_zero]
  have h : ∀ d ∈ posDiff, ncType d + ncType (-d) = 2 * nCount d := by
    intro d hd
    have hpos : 0 < d := (Finset.mem_filter.1 (by rwa [← posDiff_filter] at hd)).2
    rw [ncType_neg, ncType_of_pos hpos]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, n0Count]
  have := two_nCount_sum_le
  omega

/-- The type counts of Section 5 of `masked_digit_bound.tex` use exactly the doubled digit
budget: `∑_{d ∈ D} n_d κ(d) = 2L`. -/
theorem ncType_cost_sum :
    ∑ d ∈ carryFreeMaskData.diffSupport, ncType d * carryFreeMaskData.kappa d = 2 * Lfin := by
  rw [carryFreeMaskData.sum_diffSupport_symm (fun d => ncType d * carryFreeMaskData.kappa d),
    posDiff_filter]
  have h : ∀ d ∈ posDiff,
      ncType d * carryFreeMaskData.kappa d + ncType (-d) * carryFreeMaskData.kappa (-d)
        = 2 * (nCount d * carryFreeMaskData.kappa d) := by
    intro d hd
    have hpos : 0 < d := (Finset.mem_filter.1 (by rwa [← posDiff_filter] at hd)).2
    rw [ncType_neg, ncType_of_pos hpos, carryFreeMaskData.kappa_neg]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ncType_zero, carryFreeMaskData.kappa_zero,
    Lfin]
  simp

/-- The denominator of the multinomial count `D_N` of Section 5 of `masked_digit_bound.tex`:
`∏_{d ∈ D} n_d! = n₀! ∏_{d>0} (n_d!)²`. -/
theorem ncType_prod_factorial :
    ∏ d ∈ carryFreeMaskData.diffSupport, Nat.factorial (ncType d)
      = Nat.factorial n0Count * ∏ d ∈ posDiff, (Nat.factorial (nCount d)) ^ 2 := by
  rw [carryFreeMaskData.prod_diffSupport_symm (fun d => Nat.factorial (ncType d)),
    posDiff_filter, ncType_zero]
  have h : ∀ d ∈ posDiff,
      Nat.factorial (ncType d) * Nat.factorial (ncType (-d))
        = (Nat.factorial (nCount d)) ^ 2 := by
    intro d hd
    have hpos : 0 < d := (Finset.mem_filter.1 (by rwa [← posDiff_filter] at hd)).2
    rw [ncType_neg, ncType_of_pos hpos, sq]
  rw [Finset.prod_congr rfl h]

/-- **The difference count of Section 5 of `masked_digit_bound.tex`:** the `D_N` signed
difference words with the prescribed symmetric type give `D_N` distinct elements of
`U - U`. -/
theorem finite_difference_count_lower :
    (DNfin : ℕ) ≤ (natDiffFinset Ufin Ufin).card := by
  have hdvd := Nat.prod_factorial_dvd_factorial_sum carryFreeMaskData.diffSupport ncType
  have hDN : DNfin * (∏ d ∈ carryFreeMaskData.diffSupport, Nat.factorial (ncType d))
      = Nat.factorial Nfin := by
    rw [DNfin, Nat.div_mul_cancel hdvd, ncType_sum]
  rw [Ufin_eq]
  exact carryFreeMaskData.typeWords_card_le_natDiffFinset carryFreeMaskData_carryfree
    ncType Nfin Lfin ncType_neg ncType_sum ncType_cost_sum DNfin hDN

/-- **The multinomial count `D_N` of Section 5 of `masked_digit_bound.tex`** in the form
displayed in the source: `D_N = N! / (n₀! ∏_{d>0} (n_d!)²)`. -/
theorem DNfin_eq :
    DNfin = Nat.factorial Nfin /
      (Nat.factorial n0Count * ∏ d ∈ posDiff, (Nat.factorial (nCount d)) ^ 2) := by
  rw [DNfin, ncType_sum, ncType_prod_factorial]

/-- **The sum count of Section 5 of `masked_digit_bound.tex`:**
`|U + U| ≤ S_N = P₊(x_f)^N x_f^{-2L}`. -/
theorem finite_sum_count_upper :
    ((natSumFinset Ufin Ufin).card : ℝ) ≤
      carryFreeMaskData.Pplus (xfRat : ℝ) ^ Nfin * (xfRat : ℝ) ^ (-(2 * Lfin : ℤ)) := by
  have hxf0 : (0 : ℝ) < (xfRat : ℝ) := by norm_num [xfRat]
  have hxf1 : (xfRat : ℝ) < 1 := by norm_num [xfRat]
  -- `U + U` consists of digit arrays with digits in `S` and digit sum at most `2L`
  have hsub : natSumFinset Ufin Ufin ⊆ carryFreeMaskData.sumSet Nfin (2 * Lfin) :=
    carryFreeMaskData.natSumFinset_maskSet_subset Nfin Lfin
  have hcard : ((natSumFinset Ufin Ufin).card : ℝ)
      ≤ ((carryFreeMaskData.sumSet Nfin (2 * Lfin)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hweighted := carryFreeMaskData.sumSet_card_mul_pow_le (xfRat : ℝ) hxf0 hxf1
    Nfin (2 * Lfin)
  have hpow0 : (0 : ℝ) < (xfRat : ℝ) ^ (2 * Lfin) := pow_pos hxf0 _
  have hzpow : (xfRat : ℝ) ^ (-(2 * Lfin : ℤ)) = ((xfRat : ℝ) ^ (2 * Lfin))⁻¹ := by
    have hcast : ((2 * Lfin : ℕ) : ℤ) = 2 * (Lfin : ℤ) := by push_cast; ring
    rw [zpow_neg, ← hcast, zpow_natCast]
  rw [hzpow, ← div_eq_mul_inv, le_div_iff₀ hpow0]
  calc ((natSumFinset Ufin Ufin).card : ℝ) * (xfRat : ℝ) ^ (2 * Lfin)
      ≤ ((carryFreeMaskData.sumSet Nfin (2 * Lfin)).card : ℝ) * (xfRat : ℝ) ^ (2 * Lfin) :=
        mul_le_mul_of_nonneg_right hcard hpow0.le
    _ ≤ carryFreeMaskData.Pplus (xfRat : ℝ) ^ Nfin := hweighted

/-! ### Certified logarithm estimates for the finite-depth certificate

Section 5 of `masked_digit_bound.tex` evaluates `log D_N`, `log S_N` and `log(2Q^N)` in
`512`-bit MPFR arithmetic.  The estimates below reproduce the same three comparisons with
exact rational arithmetic, using the effective Stirling bounds of
`RequestProject/StirlingBounds.lean` for the factorials and the certified logarithm
enclosures of `RequestProject/LogNumerics.lean` for the constants. -/

/-- The total witness cost `K = ∑_{d>0} κ(d)` of the positive difference digits of Section 5
of `masked_digit_bound.tex`. -/
def cfKSum : ℕ := sumMapFold cfPosCostList id

theorem cfKSum_value : cfKSum = 221257734 := by native_decide

/-- Section 5 of `masked_digit_bound.tex` records `16184` strictly positive difference
digits. -/
theorem cfPosIdxList_length : cfPosIdxList.length = 16184 := by native_decide

/-- Every one of the `16184` type counts of Section 5 of `masked_digit_bound.tex` is positive;
the smallest of them is `n_d = 17297258`. -/
theorem cfCountAt_pos_all : cfPosCostList.all (fun c => decide (0 < cfCountAt c)) = true := by
  native_decide

theorem posDiff_index_injective :
    Function.Injective fun i : ℕ => (i : ℤ) - (carryFreeB : ℤ) := by
  intro a b hab
  simp only at hab
  have : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast this

theorem mem_posDiff_iff {d : ℤ} :
    d ∈ posDiff ↔ ∃ i ∈ cfPosIdxList, (i : ℤ) - (carryFreeB : ℤ) = d := by
  rw [posDiff_eq, List.mem_toFinset, List.mem_map]

/-- All type counts `n_d`, `d > 0`, of Section 5 of `masked_digit_bound.tex` are positive. -/
theorem nCount_pos {d : ℤ} (hd : d ∈ posDiff) : 0 < nCount d := by
  obtain ⟨i, hi, rfl⟩ := mem_posDiff_iff.1 hd
  rw [nCount_eq hi]
  have hcost : cfCostAt i ∈ cfPosCostList := by
    rw [cfPosCostList_eq]; exact List.mem_map_of_mem hi
  have h := List.all_eq_true.1 cfCountAt_pos_all _ hcost
  simpa using h

/-- The `16184` strictly positive difference digits of Section 5 of
`masked_digit_bound.tex`. -/
theorem posDiff_card : posDiff.card = 16184 := by
  rw [posDiff_eq, List.toFinset_card_of_nodup (cfPosIdxList_nodup.map posDiff_index_injective),
    List.length_map, cfPosIdxList_length]

/-- `K = ∑_{d>0} κ(d) = 221257734`, the total witness cost of the positive difference digits
of Section 5 of `masked_digit_bound.tex`. -/
theorem posDiff_kappa_sum : ∑ d ∈ posDiff, carryFreeMaskData.kappa d = 221257734 := by
  have hmap : (cfPosIdxList.map fun i : ℕ =>
      carryFreeMaskData.kappa ((i : ℤ) - (carryFreeB : ℤ))) = cfPosIdxList.map cfCostAt :=
    List.map_congr_left fun i hi => cfKappa_eq hi
  have hK : cfKSum = cfPosCostList.sum := by
    rw [cfKSum, sumMapFold_eq, List.map_id]
  rw [posDiff_sum (fun d => carryFreeMaskData.kappa d), hmap, ← cfPosCostList_eq, ← hK,
    cfKSum_value]

theorem cfWlo_ge_value : 6683247325493124 * 2 ^ 128 ≤ cfWlo * 10 ^ 13 := by native_decide

/-- **A certified lower bound for the normalizing sum `W = P₋(x_f)`** of Section 5 of
`masked_digit_bound.tex`, whose value there is `W = 668.3247325493124…`. -/
theorem Wfin_lower : (6683247325493124 / 10 ^ 13 : ℝ) ≤ Wfin := by
  have h1 : (6683247325493124 : ℝ) * 2 ^ 128 ≤ (cfWlo : ℝ) * 10 ^ 13 := by
    exact_mod_cast cfWlo_ge_value
  have h2 := cfWlo_le
  have h3 : (cfWlo : ℝ) * 10 ^ 13 ≤ (Wfin * 2 ^ 128) * 10 ^ 13 := by
    have : (0 : ℝ) ≤ 10 ^ 13 := by norm_num
    exact mul_le_mul_of_nonneg_right h2 this
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 13)]
  nlinarith [h1, h3, (by positivity : (0 : ℝ) < (2 : ℝ) ^ 128)]

/-- The fixed-point value of `P₊(x_f) · 2^128`, rounded upwards throughout. -/
def cfSpHi : ℕ :=
  sumMapFold (semiSumList carryFreeGeneratorsList carryFreeB) fun s => cfAhi.getD s 0

theorem cfSpHi_le : cfSpHi * 10 ^ 11 ≤ 9103099370522 * 2 ^ 128 := by native_decide

/-- **A certified upper bound for `P₊(x_f)`** in Section 5 of `masked_digit_bound.tex`, whose
value there is `P₊(x_f) = 91.03099370521942…`. -/
theorem Pplus_xf_upper :
    carryFreeMaskData.Pplus (xfRat : ℝ) ≤ (9103099370522 / 10 ^ 11 : ℝ) := by
  have hB : carryFreeMaskData.B = carryFreeB := rfl
  have hP := Pplus_eq_sumList carryFreeMaskData carryFreeGenerators_coe rfl (xfRat : ℝ)
  rw [hB] at hP
  have hfp := sum_pow_le (semiSumList carryFreeGeneratorsList carryFreeB) xfHi 128
    (2 * carryFreeB) (xfRat : ℝ) xfRat_nonneg xfHi_ge semiSumList_le
  have hcast : (((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
      cfAhi.getD s 0).sum : ℕ) * 10 ^ 11 ≤ (9103099370522 : ℝ) * 2 ^ 128 := by
    have h := cfSpHi_le
    rw [cfSpHi, sumMapFold_eq] at h
    exact_mod_cast h
  have hpow : (0 : ℝ) < 2 ^ 128 := by positivity
  have hstep : ((((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
      cfAhi.getD s 0).sum : ℕ) : ℝ) / 2 ^ 128 ≤ (9103099370522 / 10 ^ 11 : ℝ) := by
    rw [div_le_div_iff₀ hpow (by norm_num : (0 : ℝ) < 10 ^ 11)]
    linarith
  have hsum : ((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
      (xfRat : ℝ) ^ s).sum ≤
      ((((semiSumList carryFreeGeneratorsList carryFreeB).map fun s =>
        cfAhi.getD s 0).sum : ℕ) : ℝ) / 2 ^ 128 := by
    rw [le_div_iff₀ hpow]
    exact hfp
  rw [hP]
  linarith

/-! #### The logarithms of the constants of Section 5 -/

theorem Nfin_cast : ((Nfin : ℕ) : ℝ) = 10 ^ 13 := by norm_num [Nfin]

theorem log_Nfin_eq : Real.log (Nfin : ℝ) = 13 * Real.log 10 := by
  rw [Nfin_cast, Real.log_pow]
  norm_num

theorem xfRat_cast : ((xfRat : ℚ) : ℝ) = 9996789017186568 / 10 ^ 16 := by
  rw [xfRat]; push_cast; ring

theorem log_Wfin_lower : (650477418197 / 10 ^ 11 : ℝ) < Real.log Wfin := by
  have h := Real.log_le_log (by norm_num) Wfin_lower
  have h2 := log_W_lower
  linarith

theorem log_xfRat_lower : (-32114984443452 / 10 ^ 17 : ℝ) < Real.log (xfRat : ℝ) := by
  rw [xfRat_cast]; exact log_xf_lower

theorem log_xfRat_upper : Real.log (xfRat : ℝ) < (-32114984443451 / 10 ^ 17 : ℝ) := by
  rw [xfRat_cast]; exact log_xf_upper

/-! #### The logarithmic type-count estimates -/

/-- Since `n_d = ⌊N x_f^{κ(d)} / W⌋`, one has `log n_d ≤ log N + κ(d) log x_f − log W`; this is
the elementary bound behind the entropy estimate of Section 5 of
`masked_digit_bound.tex`. -/
theorem log_nCount_le {d : ℤ} (hd : d ∈ posDiff) :
    Real.log (nCount d : ℝ)
      ≤ Real.log (Nfin : ℝ) + (carryFreeMaskData.kappa d : ℝ) * Real.log (xfRat : ℝ)
        - Real.log Wfin := by
  have hxf0 : (0 : ℝ) < (xfRat : ℝ) := by norm_num [xfRat]
  have hN0 : (0 : ℝ) < (Nfin : ℝ) := by rw [Nfin_cast]; norm_num
  have hpk : (0 : ℝ) < (xfRat : ℝ) ^ carryFreeMaskData.kappa d := pow_pos hxf0 _
  have harg : (0 : ℝ) < (Nfin : ℝ) * (xfRat : ℝ) ^ carryFreeMaskData.kappa d / Wfin :=
    div_pos (mul_pos hN0 hpk) Wfin_pos
  have hle : (nCount d : ℝ) ≤ (Nfin : ℝ) * (xfRat : ℝ) ^ carryFreeMaskData.kappa d / Wfin :=
    Nat.floor_le harg.le
  have hpos : (0 : ℝ) < (nCount d : ℝ) := by exact_mod_cast nCount_pos hd
  have hmono := Real.log_le_log hpos hle
  rw [Real.log_div (by positivity) (ne_of_gt Wfin_pos), Real.log_mul (ne_of_gt hN0)
    (ne_of_gt hpk), Real.log_pow] at hmono
  exact hmono

/-- The entropy estimate `∑_{d>0} n_d log n_d ≤ (∑ n_d)(log N − log W) + L log x_f` of
Section 5 of `masked_digit_bound.tex`. -/
theorem sum_nCount_log_le :
    ∑ d ∈ posDiff, (nCount d : ℝ) * Real.log (nCount d : ℝ)
      ≤ 4992518598801 * (Real.log (Nfin : ℝ) - Real.log Wfin)
        + 51500691976683641 * Real.log (xfRat : ℝ) := by
  have hs1 : ∑ d ∈ posDiff, (nCount d : ℝ) = 4992518598801 := by
    rw [← Nat.cast_sum, posDiff_nCount_sum, cfNSum_value]
    norm_num
  have hL : (∑ d ∈ posDiff, nCount d * carryFreeMaskData.kappa d) = 51500691976683641 :=
    Lfin_value
  have hs2 : ∑ d ∈ posDiff, ((nCount d : ℝ) * (carryFreeMaskData.kappa d : ℝ))
      = 51500691976683641 := by
    have h : ((∑ d ∈ posDiff, nCount d * carryFreeMaskData.kappa d : ℕ) : ℝ)
        = 51500691976683641 := by rw [hL]; norm_num
    rw [← h]
    push_cast
    ring
  have hstep : ∀ d ∈ posDiff, (nCount d : ℝ) * Real.log (nCount d : ℝ)
      ≤ (nCount d : ℝ) * (Real.log (Nfin : ℝ) - Real.log Wfin)
        + ((nCount d : ℝ) * (carryFreeMaskData.kappa d : ℝ)) * Real.log (xfRat : ℝ) := by
    intro d hd
    have h := log_nCount_le hd
    have hn : (0 : ℝ) ≤ (nCount d : ℝ) := Nat.cast_nonneg _
    nlinarith [h, hn]
  calc ∑ d ∈ posDiff, (nCount d : ℝ) * Real.log (nCount d : ℝ)
      ≤ ∑ d ∈ posDiff, ((nCount d : ℝ) * (Real.log (Nfin : ℝ) - Real.log Wfin)
          + ((nCount d : ℝ) * (carryFreeMaskData.kappa d : ℝ)) * Real.log (xfRat : ℝ)) :=
        Finset.sum_le_sum hstep
    _ = 4992518598801 * (Real.log (Nfin : ℝ) - Real.log Wfin)
          + 51500691976683641 * Real.log (xfRat : ℝ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hs1, hs2]

/-- The companion estimate `∑_{d>0} log n_d ≤ 16184 (log N − log W) + K log x_f` of Section 5
of `masked_digit_bound.tex`. -/
theorem sum_log_nCount_le :
    ∑ d ∈ posDiff, Real.log (nCount d : ℝ)
      ≤ 16184 * (Real.log (Nfin : ℝ) - Real.log Wfin)
        + 221257734 * Real.log (xfRat : ℝ) := by
  have hs2 : ∑ d ∈ posDiff, (carryFreeMaskData.kappa d : ℝ) = 221257734 := by
    rw [← Nat.cast_sum, posDiff_kappa_sum]
    norm_num
  calc ∑ d ∈ posDiff, Real.log (nCount d : ℝ)
      ≤ ∑ d ∈ posDiff, ((Real.log (Nfin : ℝ) - Real.log Wfin)
          + (carryFreeMaskData.kappa d : ℝ) * Real.log (xfRat : ℝ)) :=
        Finset.sum_le_sum fun d hd => by linarith [log_nCount_le hd]
    _ = 16184 * (Real.log (Nfin : ℝ) - Real.log Wfin)
          + 221257734 * Real.log (xfRat : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, hs2, posDiff_card,
          nsmul_eq_mul]
        norm_num

/-! #### The lower bound for `log D_N` -/

theorem DNfin_mul_prod :
    DNfin * (∏ d ∈ carryFreeMaskData.diffSupport, Nat.factorial (ncType d))
      = Nat.factorial Nfin := by
  have hdvd := Nat.prod_factorial_dvd_factorial_sum carryFreeMaskData.diffSupport ncType
  rw [DNfin, Nat.div_mul_cancel hdvd, ncType_sum]

theorem ncType_ne_zero {d : ℤ} (hd : d ∈ carryFreeMaskData.diffSupport) : ncType d ≠ 0 := by
  rcases eq_or_ne d 0 with rfl | h0
  · rw [ncType_zero, n0Count_value]
    norm_num
  · have habs : |d| ∈ posDiff := by
      refine Finset.mem_filter.2 ⟨?_, abs_pos.2 h0⟩
      rcases abs_choice d with h | h
      · rw [h]; exact hd
      · rw [h]; exact carryFreeMaskData.neg_mem_diffSupport hd
    have := nCount_pos habs
    simp only [ncType, if_neg h0]
    omega

/-- **The certified lower bound for `log D_N`** of Section 5 of `masked_digit_bound.tex`.
The source reports the `512`-bit MPFR value `log D_N = 98126619915169.79448…`; the bound
proved here is weaker by roughly `2·10⁴`, which is the total loss incurred by the effective
Stirling bounds and by replacing each type count `n_d = ⌊N x_f^{κ(d)}/W⌋` by
`N x_f^{κ(d)}/W`.  It is amply sufficient for the final comparison, whose slack is more than
`4·10⁵`. -/
theorem log_DNfin_lower : (98126619896000 : ℝ) < Real.log (DNfin : ℝ) := by
  have hfac : ∀ d ∈ carryFreeMaskData.diffSupport,
      ((Nat.factorial (ncType d) : ℕ) : ℝ) ≠ 0 := fun d _ => by
    exact_mod_cast Nat.factorial_ne_zero _
  have hmul : (DNfin : ℝ) * ∏ d ∈ carryFreeMaskData.diffSupport,
      ((Nat.factorial (ncType d) : ℕ) : ℝ) = ((Nat.factorial Nfin : ℕ) : ℝ) := by
    rw [← Nat.cast_prod, ← Nat.cast_mul, DNfin_mul_prod]
  have hprod0 : (0 : ℝ) < ∏ d ∈ carryFreeMaskData.diffSupport,
      ((Nat.factorial (ncType d) : ℕ) : ℝ) :=
    Finset.prod_pos fun d _ => by exact_mod_cast Nat.factorial_pos _
  have hfac0 : (0 : ℝ) < ((Nat.factorial Nfin : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hDne : DNfin ≠ 0 := by
    intro h
    have hp := DNfin_mul_prod
    rw [h, zero_mul] at hp
    exact Nat.factorial_ne_zero Nfin hp.symm
  have hD0 : (0 : ℝ) < (DNfin : ℝ) := by
    have := Nat.pos_of_ne_zero hDne
    exact_mod_cast this
  have hlogsplit : Real.log (DNfin : ℝ)
      = Real.log ((Nat.factorial Nfin : ℕ) : ℝ)
        - ∑ d ∈ carryFreeMaskData.diffSupport,
            Real.log ((Nat.factorial (ncType d) : ℕ) : ℝ) := by
    have h := congrArg Real.log hmul
    rw [Real.log_mul (ne_of_gt hD0) (ne_of_gt hprod0), Real.log_prod hfac] at h
    linarith
  -- Stirling lower bound for `N!`
  have hNne : Nfin ≠ 0 := by norm_num [Nfin]
  have hstir := Stirling.le_log_factorial_stirling hNne
  have hlogN0 : (0 : ℝ) ≤ Real.log (Nfin : ℝ) := by
    rw [Nfin_cast]; positivity
  have hlog2pi : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlowN : (Nfin : ℝ) * Real.log (Nfin : ℝ) - (Nfin : ℝ)
      ≤ Real.log ((Nat.factorial Nfin : ℕ) : ℝ) := by linarith
  -- Stirling upper bound for the denominators
  have hupp := sum_log_factorial_le carryFreeMaskData.diffSupport ncType
    (fun d hd => ncType_ne_zero hd)
  rw [carryFree_diff_card] at hupp
  -- symmetry of the two statistics
  have hsym1 : ∑ d ∈ carryFreeMaskData.diffSupport, (ncType d : ℝ) * Real.log (ncType d : ℝ)
      = (n0Count : ℝ) * Real.log (n0Count : ℝ)
        + 2 * ∑ d ∈ posDiff, (nCount d : ℝ) * Real.log (nCount d : ℝ) := by
    rw [carryFreeMaskData.sum_diffSupport_symm
      (fun d => (ncType d : ℝ) * Real.log (ncType d : ℝ)), posDiff_filter, ncType_zero]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hpos : 0 < d := (Finset.mem_filter.1 (by rwa [← posDiff_filter] at hd)).2
    rw [ncType_neg, ncType_of_pos hpos]
    ring
  have hsym2 : ∑ d ∈ carryFreeMaskData.diffSupport, Real.log (ncType d : ℝ)
      = Real.log (n0Count : ℝ) + 2 * ∑ d ∈ posDiff, Real.log (nCount d : ℝ) := by
    rw [carryFreeMaskData.sum_diffSupport_symm (fun d => Real.log (ncType d : ℝ)),
      posDiff_filter, ncType_zero]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hpos : 0 < d := (Finset.mem_filter.1 (by rwa [← posDiff_filter] at hd)).2
    rw [ncType_neg, ncType_of_pos hpos]
    ring
  have hsum0 : ∑ d ∈ carryFreeMaskData.diffSupport, (ncType d : ℝ) = (Nfin : ℝ) := by
    rw [← Nat.cast_sum, ncType_sum]
  rw [hsym1, hsym2, hsum0] at hupp
  -- numerical constants
  have hn0 : ((n0Count : ℕ) : ℝ) = 14962802398 := by rw [n0Count_value]; norm_num
  rw [hn0] at hupp
  have hlogn0 := log_n0_upper
  have hlogW := log_Wfin_lower
  have hlogxlo := log_xfRat_lower
  have hlogxhi := log_xfRat_upper
  have h10lo := log_ten_lower
  have h10hi := log_ten_upper
  have hA := sum_nCount_log_le
  have hB := sum_log_nCount_le
  rw [log_Nfin_eq] at hA hB
  rw [log_Nfin_eq, Nfin_cast] at hlowN
  rw [Nfin_cast] at hupp
  rw [hlogsplit]
  linarith

/-- **The three logarithm comparisons of Section 5 of `masked_digit_bound.tex`.**

The source certifies them with directed `512`-bit MPFR arithmetic and reports the enclosures

`log D_N = 98126619915169.7944…`,  `log S_N = 78190878820128.0915…`,
`log(2 Q^N) = 104360257432078.3785…`.

The three bounds proved here are the same three comparisons with a deliberately relaxed
constant on each side.  Reproducing the source's enclosures to their stated `10⁻⁴` accuracy
would require a `20`-digit evaluation of all `16184` factorials entering `D_N`, whereas the
final comparison `final_explicit_finite_bound` has an absolute slack of more than `4·10⁵` in
these logarithms.  Each constant below is within `2·10⁴` of the corresponding MPFR value, on
the correct side, so the three bounds certify exactly the same conclusion. -/
theorem finite_log_bounds :
    (98126619896000 : ℝ) < Real.log (DNfin : ℝ) ∧
    Real.log (carryFreeMaskData.Pplus (xfRat : ℝ) ^ Nfin * (xfRat : ℝ) ^ (-(2 * Lfin : ℤ))) <
      (78190878820300 : ℝ) ∧
    Real.log (2 * (carryFreeQ : ℝ) ^ Nfin) < (104360257433994 : ℝ) := by
  have hxf0 : (0 : ℝ) < (xfRat : ℝ) := by norm_num [xfRat]
  refine ⟨log_DNfin_lower, ?_, ?_⟩
  · have hP0 : 0 < carryFreeMaskData.Pplus (xfRat : ℝ) := carryFreeMaskData.Pplus_pos hxf0
    have hlogP : Real.log (carryFreeMaskData.Pplus (xfRat : ℝ)) < 451120003871 / 10 ^ 11 := by
      have h := Real.log_le_log hP0 Pplus_xf_upper
      linarith [log_Pplus_upper]
    have hzc : (((-(2 * (Lfin : ℤ))) : ℤ) : ℝ) = -(2 * 51500691976683641) := by
      have hL : ((Lfin : ℕ) : ℤ) = 51500691976683641 := by exact_mod_cast Lfin_value
      rw [hL]; norm_num
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_zpow, Nfin_cast,
      hzc]
    linarith [log_xfRat_lower]
  · have hq : (carryFreeQ : ℝ) = 34065 := by norm_num [carryFreeQ]
    have h34 : Real.log 34065 < 1043602574339925 / 10 ^ 14 := by
      rw [log_34065_eq]
      linarith [log_two_upper, log_t4_upper]
    rw [hq, Real.log_mul (by norm_num) (by positivity), Real.log_pow, Nfin_cast]
    linarith [log_two_upper, h34]

/-- **Theorem 1 (Main theorem), second assertion**, equation (36)
(`eq:finite-certified`) of `masked_digit_bound.tex`: a single explicitly specified finite
set, using neither a method-of-types limit nor an infinite-block pressure, certifies

`C₃ₐ > 1.19102809`. -/
theorem final_explicit_finite_bound : (1.19102809 : ℝ) < C3a := by
  obtain ⟨hlogD, hlogS, hlogQ⟩ := finite_log_bounds
  have hxf0 : (0 : ℝ) < (xfRat : ℝ) := by norm_num [xfRat]
  set SN : ℝ := carryFreeMaskData.Pplus (xfRat : ℝ) ^ Nfin * (xfRat : ℝ) ^ (-(2 * Lfin : ℤ))
    with hSNdef
  have hSN0 : 0 < SN := by
    rw [hSNdef]
    exact mul_pos (pow_pos (carryFreeMaskData.Pplus_pos hxf0) _) (zpow_pos hxf0 _)
  -- the difference count is positive
  have hD0 : (0 : ℝ) < (DNfin : ℝ) := by
    rcases Nat.eq_zero_or_pos DNfin with hz | hz
    · rw [hz] at hlogD
      simp only [Nat.cast_zero, Real.log_zero] at hlogD
      norm_num at hlogD
    · exact_mod_cast hz
  -- the difference count exceeds the sum count
  have hSlt : SN < (DNfin : ℝ) := by
    have hlt : Real.log SN < Real.log (DNfin : ℝ) := by linarith
    calc SN = Real.exp (Real.log SN) := (Real.exp_log hSN0).symm
      _ < Real.exp (Real.log (DNfin : ℝ)) := Real.exp_lt_exp.2 hlt
      _ = (DNfin : ℝ) := Real.exp_log hD0
  have hratio : 1 ≤ (DNfin : ℝ) / SN := (one_le_div hSN0).2 hSlt.le
  -- the finite-set principle applied to `U = U_N(L)`
  have hm : 0 < Nfin := by norm_num [Nfin]
  have hL : carryFreeMaskData.B ≤ Lfin := by
    rw [Lfin_value]
    norm_num [carryFreeMaskData, carryFreeB]
  have hnd : (DNfin : ℝ) ≤
      ((natDiffFinset (carryFreeMaskData.maskSet Nfin Lfin)
        (carryFreeMaskData.maskSet Nfin Lfin)).card : ℝ) := by
    exact_mod_cast finite_difference_count_lower
  have hns : ((natSumFinset (carryFreeMaskData.maskSet Nfin Lfin)
      (carryFreeMaskData.maskSet Nfin Lfin)).card : ℝ) ≤ SN := finite_sum_count_upper
  have hghr := carryFreeMaskData.ghr_from_maskSet_estimates hm hL (DNfin : ℝ) SN hD0 hSN0
    hnd hns hratio
  -- the denominator
  have hqval : (carryFreeMaskData.q : ℝ) = (carryFreeQ : ℝ) := by
    norm_num [carryFreeMaskData]
  have hQ0 : (0 : ℝ) < (carryFreeQ : ℝ) := by norm_num [carryFreeQ]
  have hQpow : (0 : ℝ) < (carryFreeQ : ℝ) ^ Nfin := pow_pos hQ0 _
  have hlogQsplit : Real.log (2 * (carryFreeQ : ℝ) ^ Nfin)
      = Real.log 2 + (Nfin : ℝ) * Real.log (carryFreeQ : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hQpow), Real.log_pow]
  have hlog52 : Real.log 5 - Real.log 2 < 1 := by
    have hdiv : Real.log 5 - Real.log 2 = Real.log (5 / 2) :=
      (Real.log_div (by norm_num) (by norm_num)).symm
    have he : (5 : ℝ) / 2 < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      norm_num at this ⊢
      linarith
    rw [hdiv]
    calc Real.log (5 / 2) < Real.log (Real.exp 1) := Real.log_lt_log (by norm_num) he
      _ = 1 := Real.log_exp 1
  set den : ℝ := Real.log 5 + (Nfin : ℝ) * Real.log carryFreeMaskData.q with hdendef
  have hdenlt : den < 104360257433995 := by
    rw [hdendef, hqval]
    rw [hlogQsplit] at hlogQ
    linarith
  have hden0 : 0 < den := by
    have hq1 : (1 : ℝ) < (carryFreeMaskData.q : ℝ) := by
      rw [hqval]; norm_num [carryFreeQ]
    have hlogq : 0 < Real.log carryFreeMaskData.q := Real.log_pos hq1
    have hN : (0 : ℝ) < (Nfin : ℝ) := by
      have : (0 : ℕ) < Nfin := hm
      exact_mod_cast this
    have hlog5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have hprod : 0 < (Nfin : ℝ) * Real.log carryFreeMaskData.q := mul_pos hN hlogq
    rw [hdendef]
    linarith
  -- the numerator
  have hnum : (19935741075700 : ℝ) < Real.log ((DNfin : ℝ) / SN) := by
    rw [Real.log_div (ne_of_gt hD0) (ne_of_gt hSN0)]
    linarith
  -- combine
  have hstep : (19935741075700 : ℝ) / 104360257433995
      < Real.log ((DNfin : ℝ) / SN) / den := by
    have h1 : (19935741075700 : ℝ) / 104360257433995
        < Real.log ((DNfin : ℝ) / SN) / 104360257433995 :=
      (div_lt_div_iff_of_pos_right (by norm_num)).2 hnum
    have h2 : Real.log ((DNfin : ℝ) / SN) / 104360257433995
        ≤ Real.log ((DNfin : ℝ) / SN) / den :=
      div_le_div_of_nonneg_left (by linarith) hden0 hdenlt.le
    linarith
  have hfinal : (1.19102809 : ℝ) < 1 + Real.log ((DNfin : ℝ) / SN) / den := by
    have : (0.19102809 : ℝ) < (19935741075700 : ℝ) / 104360257433995 := by
      norm_num
    linarith
  linarith [hghr]

end MaskedDigit

