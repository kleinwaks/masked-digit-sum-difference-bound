import RequestProject.CertBasic

/-!
# The fixed-point weight tables of the certificate

The kernel `CertKernel.Basic` evaluates the powers `x ^ a` of the fugacity
`x = 0x1.ffde827adc0fep-1` of equation (34) (`eq:controlled-x`) of `masked_digit_bound.tex`
in exact fixed-point arithmetic: `wt a = (m, e)` is a *lower* bound `m · 2^{-e} ≤ x ^ a` and
`wtU a = (m, e)` an *upper* bound `x ^ a ≤ m · 2^{-e}`, both with a 64-bit mantissa.

This file proves those two bounds, together with the versions actually used in the row sums,
where the mantissa is truncated to 32 bits (`m32L`, `e32L`, `m32U`, `e32U`).
-/

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace MaskedDigit

open CertKernel

/-- The fugacity `x = 0x1.ffde827adc0fep-1 = XN / 2 ^ 52` of equation (34)
(`eq:controlled-x`) of `masked_digit_bound.tex`, as a real number. -/
noncomputable def xR : ℝ := (XN : ℝ) / 2 ^ 52

theorem xR_pos : 0 < xR := by
  rw [xR]; norm_num [XN]

theorem xR_lt_one : xR < 1 := by
  rw [xR, div_lt_one (by positivity)]
  norm_num [XN]

theorem xR_le_one : xR ≤ 1 := xR_lt_one.le

/-! ## The unfolding equations of the two recursions -/

theorem iterF_succ {α : Type _} (f : α → α) (a0 : α) (n : ℕ) :
    iterF f a0 (n + 1) = f (iterF f a0 n) := rfl

theorem wt_zero : wt 0 = (2 ^ 63, 63) := rfl

theorem wt_succ (a : ℕ) : wt (a + 1) = wtStep (wt a) := by
  rw [wt, wt, iterF_succ]

theorem wtU_zero : wtU 0 = (2 ^ 63, 63) := rfl

theorem wtU_succ (a : ℕ) : wtU (a + 1) = wtStepU (wtU a) := by
  rw [wtU, wtU, iterF_succ]

theorem wtStep_eq (p : ℕ × ℕ) :
    wtStep p =
      if 2 ^ 63 ≤ (p.1 * XN) >>> 52 then ((p.1 * XN) >>> 52, p.2)
      else ((p.1 * XN) >>> 51, p.2 + 1) := rfl

theorem wtStepU_eq (p : ℕ × ℕ) :
    wtStepU p =
      if 2 ^ 63 ≤ ceilShift (p.1 * XN) 52 then (ceilShift (p.1 * XN) 52, p.2)
      else (ceilShift (p.1 * XN) 51, p.2 + 1) := rfl

/-! ## The exponents -/

theorem wt_exp_ge : ∀ a : ℕ, 63 ≤ (wt a).2
  | 0 => le_refl _
  | a + 1 => by
      rw [wt_succ, wtStep_eq]
      have := wt_exp_ge a
      split_ifs <;> simp <;> omega

theorem wtU_exp_ge : ∀ a : ℕ, 63 ≤ (wtU a).2
  | 0 => le_refl _
  | a + 1 => by
      rw [wtU_succ, wtStepU_eq]
      have := wtU_exp_ge a
      split_ifs <;> simp <;> omega

/-! ## The two mantissa bounds -/

theorem wt_le : ∀ a : ℕ, ((wt a).1 : ℝ) ≤ xR ^ a * 2 ^ ((wt a).2)
  | 0 => by rw [wt_zero]; norm_num
  | a + 1 => by
      have ih := wt_le a
      have hx0 : (0 : ℝ) < xR := xR_pos
      have hXN : ((wt a).1 : ℝ) * XN / 2 ^ 52 = ((wt a).1 : ℝ) * xR := by
        rw [xR]; ring
      have hstep : (((wt a).1 * XN : ℕ) : ℝ) = ((wt a).1 : ℝ) * (XN : ℝ) := by push_cast; ring
      rw [wt_succ, wtStep_eq]
      split_ifs with h <;> dsimp only
      · refine le_trans (cast_shiftRight_le _ 52) ?_
        rw [hstep]
        have : ((wt a).1 : ℝ) * (XN : ℝ) / 2 ^ 52 = ((wt a).1 : ℝ) * xR := by rw [xR]; ring
        rw [this]
        have := mul_le_mul_of_nonneg_right ih hx0.le
        calc ((wt a).1 : ℝ) * xR ≤ (xR ^ a * 2 ^ ((wt a).2)) * xR := this
          _ = xR ^ (a + 1) * 2 ^ ((wt a).2) := by ring
      · refine le_trans (cast_shiftRight_le _ 51) ?_
        rw [hstep]
        have h2 : ((wt a).1 : ℝ) * (XN : ℝ) / 2 ^ 51 = 2 * (((wt a).1 : ℝ) * xR) := by
          rw [xR]; ring
        rw [h2]
        have := mul_le_mul_of_nonneg_right ih hx0.le
        calc 2 * (((wt a).1 : ℝ) * xR) ≤ 2 * ((xR ^ a * 2 ^ ((wt a).2)) * xR) := by linarith
          _ = xR ^ (a + 1) * 2 ^ ((wt a).2 + 1) := by rw [pow_succ]; ring

theorem le_wtU : ∀ a : ℕ, xR ^ a * 2 ^ ((wtU a).2) ≤ ((wtU a).1 : ℝ)
  | 0 => by rw [wtU_zero]; norm_num
  | a + 1 => by
      have ih := le_wtU a
      have hx0 : (0 : ℝ) < xR := xR_pos
      have hstep : (((wtU a).1 * XN : ℕ) : ℝ) = ((wtU a).1 : ℝ) * (XN : ℝ) := by push_cast; ring
      rw [wtU_succ, wtStepU_eq]
      split_ifs with h <;> dsimp only
      · refine le_trans ?_ (le_cast_ceilShift ((wtU a).1 * XN) 52)
        rw [hstep]
        have h2 : ((wtU a).1 : ℝ) * (XN : ℝ) / 2 ^ 52 = ((wtU a).1 : ℝ) * xR := by rw [xR]; ring
        rw [h2]
        have := mul_le_mul_of_nonneg_right ih hx0.le
        calc xR ^ (a + 1) * 2 ^ ((wtU a).2) = (xR ^ a * 2 ^ ((wtU a).2)) * xR := by ring
          _ ≤ ((wtU a).1 : ℝ) * xR := this
      · refine le_trans ?_ (le_cast_ceilShift ((wtU a).1 * XN) 51)
        rw [hstep]
        have h2 : ((wtU a).1 : ℝ) * (XN : ℝ) / 2 ^ 51 = 2 * (((wtU a).1 : ℝ) * xR) := by
          rw [xR]; ring
        rw [h2]
        have := mul_le_mul_of_nonneg_right ih hx0.le
        calc xR ^ (a + 1) * 2 ^ ((wtU a).2 + 1) = 2 * ((xR ^ a * 2 ^ ((wtU a).2)) * xR) := by
              rw [pow_succ]; ring
          _ ≤ 2 * (((wtU a).1 : ℝ) * xR) := by linarith

/-! ## The tabulated 32-bit versions -/

theorem wtArr_getD {a : ℕ} (h : a ≤ WSZ) : wtArr.getD a (0, 0) = wt a :=
  kernelIterArr_getD wtStep (0, 0) (2 ^ 63, 63) h

theorem wtArrU_getD {a : ℕ} (h : a ≤ WSZ) : wtArrU.getD a (0, 0) = wtU a :=
  kernelIterArr_getD wtStepU (0, 0) (2 ^ 63, 63) h

theorem m32L_getD {a : ℕ} (h : a ≤ WSZ) : m32L.getD a 0 = (wt a).1 >>> 32 := by
  rw [m32L, tabArr_getD _ _ (by omega : a < WSZ + 1), wtArr_getD h]

theorem e32L_getD {a : ℕ} (h : a ≤ WSZ) : e32L.getD a 0 = (wt a).2 - 32 := by
  rw [e32L, tabArr_getD _ _ (by omega : a < WSZ + 1), wtArr_getD h]

theorem m32U_getD {a : ℕ} (h : a ≤ WSZ) : m32U.getD a 0 = ((wtU a).1 >>> 32) + 1 := by
  rw [m32U, tabArr_getD _ _ (by omega : a < WSZ + 1), wtArrU_getD h]

theorem e32U_getD {a : ℕ} (h : a ≤ WSZ) : e32U.getD a 0 = (wtU a).2 - 32 := by
  rw [e32U, tabArr_getD _ _ (by omega : a < WSZ + 1), wtArrU_getD h]

/-- The exponent used in the difference-side row sums exceeds the fixed-point scale `EE`. -/
theorem EE_le_e32L {a : ℕ} (h : a ≤ WSZ) : EE ≤ e32L.getD a 0 := by
  rw [e32L_getD h]
  have := wt_exp_ge a
  simp [EE]
  omega

/-- The exponent used in the sum-side row sums exceeds the fixed-point scale `EE`. -/
theorem EE_le_e32U {a : ℕ} (h : a ≤ WSZ) : EE ≤ e32U.getD a 0 := by
  rw [e32U_getD h]
  have := wtU_exp_ge a
  simp [EE]
  omega

/-- **The truncated lower weight table is a lower bound for `x ^ a`.** -/
theorem m32L_le {a : ℕ} (h : a ≤ WSZ) :
    ((m32L.getD a 0 : ℕ) : ℝ) ≤ xR ^ a * 2 ^ (e32L.getD a 0) := by
  have he := wt_exp_ge a
  rw [m32L_getD h, e32L_getD h]
  refine le_trans (cast_shiftRight_le _ 32) ?_
  have hsplit : ((wt a).2 : ℕ) = ((wt a).2 - 32) + 32 := by omega
  rw [div_le_iff₀ (by positivity)]
  calc ((wt a).1 : ℝ) ≤ xR ^ a * 2 ^ ((wt a).2) := wt_le a
    _ = xR ^ a * 2 ^ ((wt a).2 - 32) * 2 ^ 32 := by
        rw [show ((2 : ℝ) ^ ((wt a).2)) = 2 ^ ((wt a).2 - 32) * 2 ^ 32 by
          rw [← pow_add, ← hsplit]]
        ring

/-- **The truncated upper weight table is an upper bound for `x ^ a`.** -/
theorem le_m32U {a : ℕ} (h : a ≤ WSZ) :
    xR ^ a * 2 ^ (e32U.getD a 0) ≤ ((m32U.getD a 0 : ℕ) : ℝ) := by
  have he := wtU_exp_ge a
  rw [m32U_getD h, e32U_getD h]
  have hceil : ((wtU a).1 : ℝ) / 2 ^ 32 ≤ (((wtU a).1 >>> 32 : ℕ) : ℝ) + 1 := by
    refine le_trans (le_cast_ceilShift ((wtU a).1) 32) ?_
    have : ceilShift ((wtU a).1) 32 ≤ ((wtU a).1 >>> 32) + 1 := by
      rw [show ceilShift ((wtU a).1) 32 =
        if (((wtU a).1 >>> 32) <<< 32 == (wtU a).1) = true then (wtU a).1 >>> 32
        else (wtU a).1 >>> 32 + 1 from rfl]
      split_ifs <;> omega
    exact_mod_cast this
  have hsplit : ((wtU a).2 : ℕ) = ((wtU a).2 - 32) + 32 := by omega
  have hkey : xR ^ a * 2 ^ ((wtU a).2 - 32) ≤ ((wtU a).1 : ℝ) / 2 ^ 32 := by
    rw [le_div_iff₀ (by positivity)]
    calc xR ^ a * 2 ^ ((wtU a).2 - 32) * 2 ^ 32 = xR ^ a * 2 ^ ((wtU a).2) := by
          rw [show ((2 : ℝ) ^ ((wtU a).2)) = 2 ^ ((wtU a).2 - 32) * 2 ^ 32 by
            rw [← pow_add, ← hsplit]]
          ring
      _ ≤ ((wtU a).1 : ℝ) := le_wtU a
  refine le_trans hkey (le_trans hceil (le_of_eq ?_))
  push_cast
  ring

end MaskedDigit
