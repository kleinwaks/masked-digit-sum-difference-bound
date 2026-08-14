import RequestProject.CertBasic

/-!
# Evaluation of the difference-side Collatz--Wielandt check

This file runs the difference-side half of the verification of Section 4.3 of
`masked_digit_bound.tex`: the positive vector shipped with the certificate data satisfies the
Collatz--Wielandt inequality of equation (32) (`eq:controlled-collatz`) at every state of the
truncated carry graph, with ratio `582.117820`.
-/

namespace MaskedDigit

/-- Every entry of the difference-side certificate vector is positive. -/
theorem diffVPos_true : CertKernel.diffVPos () = true := by native_decide

/-- **The difference-side Collatz--Wielandt check.**  At every state `s` of the truncated
carry graph, `582.117820 · V s ≤ ∑_r x^{a(s,r)} V(Φ(s,r))`, in the kernel's exact fixed-point
arithmetic. -/
theorem diffCheck_true : CertKernel.diffCheck () = true := by native_decide

end MaskedDigit
