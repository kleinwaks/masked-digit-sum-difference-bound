import RequestProject.CertDiff
import RequestProject.CertSum
import RequestProject.LogBounds

/-!
# The controlled-carry certificate

This file formalizes Section 4.3 ("The controlled-carry certificate") of
`masked_digit_bound.tex`, culminating in the first assertion of Theorem 1
(`thm:main`), equation (35) (`eq:controlled-certified`):

`C₃ₐ > 1.19519192`.

The data are those of equations (33) (`eq:controlled-mask`) and (34) (`eq:controlled-x`):
`B = 26972`, `q = 27022`, `M = ⟨1971, 2016, 2100, 2628, 2688, 2800⟩ ∩ [0, B]` and
`x = 0x1.ffde827adc0fep-1`.

The two large computational facts — the positive-vector (Collatz--Wielandt) certificate for
the difference operator and the one for the sum operator — are verified by the certificate
kernel `CertKernel.Basic` and assembled in `RequestProject.CertDiff` and
`RequestProject.CertSum`; they are restated here, for the fugacity `finalX`, as
`final_difference_certificate` and `final_sum_certificate`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

open scoped BigOperators
open Classical

namespace MaskedDigit

/-! ## Discrete reconstruction -/

/-- `|M| = 5869`, the mask cardinality reported in Section 4.3 of
`masked_digit_bound.tex`.  This is one of the discrete facts reconstructed by the
verification package. -/
theorem final_mask_card : finalMaskData.M.card = 5869 := by
  rw [finalMaskData_M,
    generatedUpTo_card finalGenerators_coe]
  native_decide

/-- `|M + M| = 31274`, the sum-support cardinality reported in Section 4.3 of
`masked_digit_bound.tex`. -/
theorem final_sum_card : finalMaskData.sumSupport.card = 31274 := by
  have hM : finalMaskData.M = generatedUpTo finalGenerators finalMaskData.B := by
    rw [finalMaskData_M, finalMaskData_B]
  rw [sumSupport_card finalMaskData finalGenerators_coe hM, finalMaskData_B]
  native_decide

/-! ## The two large certificate facts -/

/-- The fugacity `x = 0x1.ffde827adc0fep-1` of equation (34) (`eq:controlled-x`) of
`masked_digit_bound.tex`, as a rational and as the real number used by the certificate
kernel, are the same number. -/
theorem finalX_eq_xR : ((finalX : ℚ) : ℝ) = xR := by
  rw [finalX, xR]
  norm_num [CertKernel.XN]

/-- **The difference-side certificate of Section 4.3 of `masked_digit_bound.tex`:**
equation (32) (`eq:controlled-collatz`).  The source exhibits a positive dyadic vector on the
`351951`-state accessible subgraph `F₈` with `T_{x,F₈} v > 582.117820 v` componentwise, whence
`ρ(T_{x,F₈}) > 582.117820` and, by Proposition 6, `log 582.117820 ≤ 𝒫₋(x)`.

The formalized proof establishes the same conclusion by the same Collatz--Wielandt principle,
but on the truncated carry automaton of `RequestProject.CertDiff`; see
`MaskedDigit.log_cCert_le_PminusPressure`. -/
theorem final_difference_certificate :
    Real.log (cCert : ℝ) ≤ finalMaskData.PminusPressure (finalX : ℝ) := by
  rw [finalX_eq_xR]
  exact log_cCert_le_PminusPressure

/-- **The sum-side certificate of Section 4.3 of `masked_digit_bound.tex`:** the source's
directed `8192`-digit dynamic program gives `W_{8192}(x)^{1/8192} < 79.428331`, whence
`𝒫₊(x) ≤ log 79.428331`.

The formalized proof establishes the same conclusion by a Collatz--Wielandt vector for the
truncated carry automaton of `RequestProject.CertSum`; see
`MaskedDigit.PplusPressure_le_log_pCert`. -/
theorem final_sum_certificate :
    finalMaskData.PplusPressure (finalX : ℝ) ≤ Real.log (pCert : ℝ) := by
  rw [finalX_eq_xR]
  exact PplusPressure_le_log_pCert

/-- The exact logarithm comparison certified by the rational-arithmetic script of Section 4.3
of `masked_digit_bound.tex`:
`1 + log(582.117820 / 79.428331) / log 27022 > 1.19519192`. -/
theorem final_log_comparison :
    (1.19519192 : ℝ) <
      1 + Real.log ((582117820 : ℝ) / 79428331) / Real.log 27022 := by
  have hpos : 0 < Real.log 27022 := log_27022_pos
  have h := exponent_comparison
  have hdiv : (0.19519192 : ℝ) < Real.log ((582117820 : ℝ) / 79428331) / Real.log 27022 :=
    (lt_div_iff₀ hpos).2 h
  linarith

/-- **Theorem 1 (Main theorem), first assertion**, equation (35)
(`eq:controlled-certified`) of `masked_digit_bound.tex`:

`C₃ₐ > 1.19519192`. -/
theorem final_controlled_carry_bound : (1.19519192 : ℝ) < C3a := by
  have hx0 : (0 : ℝ) < (finalX : ℝ) := by norm_num [finalX]
  have hx1 : (finalX : ℝ) < 1 := by norm_num [finalX]
  have hc : (0 : ℝ) < (cCert : ℝ) := by norm_num [cCert]
  have hp : (0 : ℝ) < (pCert : ℝ) := by norm_num [pCert]
  have hcert := finalMaskData.finite_pressure_certificate (finalX : ℝ) (cCert : ℝ)
    (pCert : ℝ) hx0 hx1 hc hp final_difference_certificate final_sum_certificate
  have hq : (finalMaskData.q : ℝ) = 27022 := by rw [finalMaskData_q]; norm_num [finalQ]
  have hratio : ((cCert : ℝ) / (pCert : ℝ)) = (582117820 : ℝ) / 79428331 := by
    norm_num [cCert, pCert]
  rw [hq, hratio] at hcert
  exact lt_of_lt_of_le final_log_comparison hcert

end MaskedDigit
