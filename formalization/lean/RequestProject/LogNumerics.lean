import RequestProject.LogBounds

/-!
# High-precision certified logarithm enclosures for the finite-depth certificate

Section 5 of `masked_digit_bound.tex` evaluates the logarithms occurring in the finite-depth
certificate — `log 2`, `log 10` (through `log N` with `N = 10¹³`), `log x_f`, `log W`,
`log P₊(x_f)` and `log n₀` — in `512`-bit MPFR arithmetic with directed rounding.

This file is the Lean counterpart of that evaluation.  Every enclosure below is obtained from
the Mercator series `log (1 - x) = -∑_{i<n} x^{i+1}/(i+1) + O(|x|^{n+1}/(1-|x|))` of
`RequestProject/LogBounds.lean`, evaluated in exact rational arithmetic after an argument
reduction of the form `a = 2^k · (a / 2^k)`.

The precision produced here (roughly `10⁻¹⁴` relative) is far below the `512`-bit precision of
the source, but is amply sufficient for the certificate: the final comparison of Section 5 has
an absolute slack of more than `4·10⁵` in the logarithms, whereas the enclosures below
contribute a total error of well under `10³`.
-/

namespace MaskedDigit

set_option maxRecDepth 40000

/-! ## `log 2` -/

/-- A certified lower bound for `log 2`, refining Mathlib's `Real.log_two_gt_d9` to the
precision needed by the finite-depth certificate of Section 5 of `masked_digit_bound.tex`. -/
theorem log_two_lower : (69314718055994 / 10 ^ 14 : ℝ) < Real.log 2 := by
  have hx : |(1 / 2 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 50
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  rw [habs] at h
  have hl : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rw [hl, Real.log_inv] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log 2`, refining Mathlib's `Real.log_two_lt_d9` to the
precision needed by the finite-depth certificate of Section 5 of `masked_digit_bound.tex`. -/
theorem log_two_upper : Real.log 2 < (69314718055995 / 10 ^ 14 : ℝ) := by
  have hx : |(1 / 2 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_lower hx 50
  have habs : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_nonneg (by norm_num)
  rw [habs] at h
  have hl : (1 : ℝ) - 1 / 2 = 2⁻¹ := by norm_num
  rw [hl, Real.log_inv] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-! ## `log 10` -/

/-- A certified lower bound for `log (5/4)`, the reduced argument used for `log 10`. -/
theorem log_five_fourths_lower : (22314355131420 / 10 ^ 14 : ℝ) < Real.log (5 / 4) := by
  have hx : |(-1 / 4 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_lower hx 24
  have habs : |(-1 / 4 : ℝ)| = 1 / 4 := by rw [abs_of_nonpos] <;> norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - -1 / 4 = 5 / 4 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log (5/4)`, the reduced argument used for `log 10`. -/
theorem log_five_fourths_upper : Real.log (5 / 4) < (22314355131422 / 10 ^ 14 : ℝ) := by
  have hx : |(-1 / 4 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 24
  have habs : |(-1 / 4 : ℝ)| = 1 / 4 := by rw [abs_of_nonpos] <;> norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - -1 / 4 = 5 / 4 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The argument reduction `log 10 = 3 log 2 + log (5/4)`. -/
theorem log_ten_eq : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
  have hval : (10 : ℝ) = 2 ^ 3 * (5 / 4) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  norm_num

/-- A certified lower bound for `log 10`, used for `log N` with `N = 10¹³` in Section 5 of
`masked_digit_bound.tex`. -/
theorem log_ten_lower : (230258509299402 / 10 ^ 14 : ℝ) < Real.log 10 := by
  rw [log_ten_eq]
  linarith [log_two_lower, log_five_fourths_lower]

/-- A certified upper bound for `log 10`, used for `log N` with `N = 10¹³` in Section 5 of
`masked_digit_bound.tex`. -/
theorem log_ten_upper : Real.log 10 < (230258509299407 / 10 ^ 14 : ℝ) := by
  rw [log_ten_eq]
  linarith [log_two_upper, log_five_fourths_upper]

/-! ## `log x_f` -/

/-- A certified lower bound for `log x_f`, where `x_f = 0.9996789017186568` is the fugacity of
Section 5 of `masked_digit_bound.tex`. -/
theorem log_xf_lower :
    (-32114984443452 / 10 ^ 17 : ℝ) < Real.log (9996789017186568 / 10 ^ 16) := by
  have hx : |(3210982813432 / 10 ^ 16 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_lower hx 5
  have habs : |(3210982813432 / 10 ^ 16 : ℝ)| = 3210982813432 / 10 ^ 16 := by
    rw [abs_of_nonneg]; norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - 3210982813432 / 10 ^ 16 = 9996789017186568 / 10 ^ 16 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log x_f`, where `x_f = 0.9996789017186568` is the fugacity of
Section 5 of `masked_digit_bound.tex`. -/
theorem log_xf_upper :
    Real.log (9996789017186568 / 10 ^ 16) < (-32114984443451 / 10 ^ 17 : ℝ) := by
  have hx : |(3210982813432 / 10 ^ 16 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 5
  have habs : |(3210982813432 / 10 ^ 16 : ℝ)| = 3210982813432 / 10 ^ 16 := by
    rw [abs_of_nonneg]; norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - 3210982813432 / 10 ^ 16 = 9996789017186568 / 10 ^ 16 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-! ## `log W` -/

/-- A certified lower bound for `log (W/512)`, the reduced argument used for the normalizing
sum `W = P₋(x_f) ≈ 668.32473254931` of Section 5 of `masked_digit_bound.tex`. -/
theorem log_W_reduced_lower :
    (26644955694 / 10 ^ 11 : ℝ) < Real.log (6683247325493124 / 5120000000000000) := by
  have hx : |(-1563247325493124 / 5120000000000000 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_lower hx 22
  have habs : |(-1563247325493124 / 5120000000000000 : ℝ)|
      = 1563247325493124 / 5120000000000000 := by
    rw [abs_of_nonpos] <;> norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - -1563247325493124 / 5120000000000000
      = 6683247325493124 / 5120000000000000 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified lower bound for `log W` with `W ≥ 668.3247325493124`, the normalizing sum of
Section 5 of `masked_digit_bound.tex`. -/
theorem log_W_lower :
    (650477418197 / 10 ^ 11 : ℝ) < Real.log (6683247325493124 / 10 ^ 13) := by
  have hval : (6683247325493124 / 10 ^ 13 : ℝ)
      = 2 ^ 9 * (6683247325493124 / 5120000000000000) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have := log_W_reduced_lower
  have := log_two_lower
  push_cast
  linarith

/-! ## `log P₊(x_f)` -/

/-- A certified upper bound for `log (P₊/128)`, the reduced argument used for
`P₊(x_f) ≈ 91.03099370522` in Section 5 of `masked_digit_bound.tex`. -/
theorem log_Pplus_reduced_upper :
    Real.log (9103099370522 / 12800000000000) < (-34083022521 / 10 ^ 11 : ℝ) := by
  have hx : |(3696900629478 / 12800000000000 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 20
  have habs : |(3696900629478 / 12800000000000 : ℝ)| = 3696900629478 / 12800000000000 := by
    rw [abs_of_nonneg]; norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - 3696900629478 / 12800000000000
      = 9103099370522 / 12800000000000 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log P₊(x_f)` with `P₊(x_f) ≤ 91.03099370522`, the sum-side
partition function of Section 5 of `masked_digit_bound.tex`. -/
theorem log_Pplus_upper :
    Real.log (9103099370522 / 10 ^ 11) < (451120003871 / 10 ^ 11 : ℝ) := by
  have hval : (9103099370522 / 10 ^ 11 : ℝ)
      = 2 ^ 7 * (9103099370522 / 12800000000000) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have := log_Pplus_reduced_upper
  have := log_two_upper
  push_cast
  linarith

/-! ## `log n₀` -/

/-- A certified upper bound for `log (n₀ / 2³⁴)`, the reduced argument used for the zero-digit
count `n₀ = 14962802398` of Section 5 of `masked_digit_bound.tex`. -/
theorem log_n0_reduced_upper :
    Real.log (14962802398 / 17179869184) < (-13817102101 / 10 ^ 11 : ℝ) := by
  have hx : |(2217066786 / 17179869184 : ℝ)| < 1 := by rw [abs_lt]; norm_num
  have h := log_one_sub_upper hx 14
  have habs : |(2217066786 / 17179869184 : ℝ)| = 2217066786 / 17179869184 := by
    rw [abs_of_nonneg]; norm_num
  rw [habs] at h
  have hl : (1 : ℝ) - 2217066786 / 17179869184 = 14962802398 / 17179869184 := by norm_num
  rw [hl] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- A certified upper bound for `log n₀` with `n₀ = 14962802398`, the zero-digit count of
Section 5 of `masked_digit_bound.tex`. -/
theorem log_n0_upper : Real.log 14962802398 < (2342883311803 / 10 ^ 11 : ℝ) := by
  have hval : (14962802398 : ℝ) = 2 ^ 34 * (14962802398 / 17179869184) := by norm_num
  rw [hval, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
  have := log_n0_reduced_upper
  have := log_two_upper
  push_cast
  linarith

end MaskedDigit
