import RequestProject.CertBasic

/-!
# Evaluation of the sum-side Collatz--Wielandt check

This file runs the sum-side half of the verification of Section 4.3 of
`masked_digit_bound.tex`: the positive vector obtained from the directed dynamic program of
Section 4.1 satisfies the Collatz--Wielandt inequality at every state of the truncated carry
graph, with ratio `79.428331`.
-/

namespace MaskedDigit

/-- Every entry of the sum-side certificate vector is positive. -/
theorem sumVPos_true : CertKernel.sumVPos () = true := by native_decide

/-- **The sum-side Collatz--Wielandt check.**  At every state `s`,
`∑_r x^{cost(s,r)} V(Φ(s,r)) ≤ 79.428331 · V s`, in the kernel's exact fixed-point
arithmetic. -/
theorem sumRowCheck_true : CertKernel.sumRowCheck () = true := by native_decide

end MaskedDigit
