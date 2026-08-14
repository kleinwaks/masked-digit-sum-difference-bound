import RequestProject.MaskData

/-!
# The balancing condition at an interior optimum

This file formalizes the Remark "The balancing condition at an interior optimum"
(`rem:moment`) of Section 2 of `masked_digit_bound.tex`.

Parameterizing `x = e^{-λ}` with `λ > 0` and writing

`F(λ) = log P₋(e^{-λ}) − log P₊(e^{-λ})`,

giving the sum support `S` the probability weights proportional to `e^{-λ s}` and the
difference support `D` the probability weights proportional to `e^{-λ κ(d)}`, the source
computes

`F'(λ) = E₊[s] − E₋[κ(d)]`,

so that every interior stationary point satisfies `E₊[s] = E₋[κ(d)]`.  As the source notes,
this identity is not used in the proof of any of its bounds.
-/

open scoped BigOperators

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-- The objective `F(λ) = log P₋(e^{-λ}) − log P₊(e^{-λ})` of the Remark
"The balancing condition at an interior optimum" (`rem:moment`) of
`masked_digit_bound.tex`. -/
noncomputable def logRatio (lam : ℝ) : ℝ :=
  Real.log (D.Pminus (Real.exp (-lam))) - Real.log (D.Pplus (Real.exp (-lam)))

/-- The sum-side partition function `∑_{s ∈ S} e^{-λ s}`, i.e. `P₊(e^{-λ})`. -/
noncomputable def expSumPartition (lam : ℝ) : ℝ := ∑ s ∈ D.sumSupport, Real.exp (-(lam * s))

/-- The difference-side partition function `∑_{d ∈ D} e^{-λ κ(d)}`, i.e. `P₋(e^{-λ})`. -/
noncomputable def expDiffPartition (lam : ℝ) : ℝ :=
  ∑ d ∈ D.diffSupport, Real.exp (-(lam * D.kappa d))

/-- The mean sum digit `E₊[s]` for the probability weights proportional to `e^{-λ s}` on the
sum support, from the Remark `rem:moment` of `masked_digit_bound.tex`. -/
noncomputable def meanSumDigit (lam : ℝ) : ℝ :=
  (∑ s ∈ D.sumSupport, (s : ℝ) * Real.exp (-(lam * s))) / D.expSumPartition lam

/-- The mean minimum witness cost `E₋[κ(d)]` for the probability weights proportional to
`e^{-λ κ(d)}` on the difference support, from the Remark `rem:moment` of
`masked_digit_bound.tex`. -/
noncomputable def meanWitnessCost (lam : ℝ) : ℝ :=
  (∑ d ∈ D.diffSupport, (D.kappa d : ℝ) * Real.exp (-(lam * D.kappa d))) / D.expDiffPartition lam

/-- The sum-side partition function `P₊(e^{-λ})` of the Remark `rem:moment` of `masked_digit_bound.tex` is positive. -/
theorem expSumPartition_pos (lam : ℝ) : 0 < D.expSumPartition lam :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) D.sumSupport_nonempty

/-- The difference-side partition function `P₋(e^{-λ})` of the Remark `rem:moment` of `masked_digit_bound.tex` is positive. -/
theorem expDiffPartition_pos (lam : ℝ) : 0 < D.expDiffPartition lam :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) D.diffSupport_nonempty

/-- The substitution `x = e^{-λ}` of the Remark `rem:moment` of `masked_digit_bound.tex` turns `P₊(x)` into `∑_{s ∈ S} e^{-λ s}`. -/
theorem Pplus_exp_eq (lam : ℝ) : D.Pplus (Real.exp (-lam)) = D.expSumPartition lam := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The substitution `x = e^{-λ}` of the Remark `rem:moment` of `masked_digit_bound.tex` turns `P₋(x)` into `∑_{d ∈ D} e^{-λ κ(d)}`. -/
theorem Pminus_exp_eq (lam : ℝ) : D.Pminus (Real.exp (-lam)) = D.expDiffPartition lam := by
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Real.exp_nat_mul]
  ring_nf

/-- The function `F(λ) = log P₋(e^{-λ}) - log P₊(e^{-λ})` of the Remark `rem:moment` of `masked_digit_bound.tex`, written in terms of the two exponential partition functions. -/
theorem logRatio_eq (lam : ℝ) :
    D.logRatio lam = Real.log (D.expDiffPartition lam) - Real.log (D.expSumPartition lam) := by
  rw [logRatio, Pplus_exp_eq, Pminus_exp_eq]

/-- Differentiation of the sum-side partition function `λ ↦ ∑_{s ∈ S} e^{-λ s}`, the first step of the Remark `rem:moment` of `masked_digit_bound.tex`. -/
theorem hasDerivAt_expSumPartition (lam : ℝ) :
    HasDerivAt D.expSumPartition (-∑ s ∈ D.sumSupport, (s : ℝ) * Real.exp (-(lam * s))) lam := by
  have key : ∀ s : ℕ, HasDerivAt (fun t : ℝ => Real.exp (-(t * (s : ℝ))))
      (-((s : ℝ) * Real.exp (-(lam * s)))) lam := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => -(t * (s : ℝ))) (-(s : ℝ)) lam := by
      simpa using ((hasDerivAt_id lam).mul_const (s : ℝ)).neg
    have h2 := h1.exp
    convert h2 using 1
    ring
  have h := HasDerivAt.sum (u := D.sumSupport)
    (A := fun (s : ℕ) (t : ℝ) => Real.exp (-(t * (s : ℝ))))
    (A' := fun s : ℕ => -((s : ℝ) * Real.exp (-(lam * s)))) (x := lam) (fun s _ => key s)
  rw [Finset.sum_neg_distrib] at h
  have heq : (∑ i ∈ D.sumSupport, (fun (s : ℕ) (t : ℝ) => Real.exp (-(t * (s : ℝ)))) i)
      = D.expSumPartition := by
    funext t
    simp [expSumPartition, Finset.sum_apply]
  rwa [heq] at h

/-- Differentiation of the difference-side partition function `λ ↦ ∑_{d ∈ D} e^{-λ κ(d)}`, the second step of the Remark `rem:moment` of `masked_digit_bound.tex`. -/
theorem hasDerivAt_expDiffPartition (lam : ℝ) :
    HasDerivAt D.expDiffPartition
      (-∑ d ∈ D.diffSupport, (D.kappa d : ℝ) * Real.exp (-(lam * D.kappa d))) lam := by
  have key : ∀ k : ℕ, HasDerivAt (fun t : ℝ => Real.exp (-(t * (k : ℝ))))
      (-((k : ℝ) * Real.exp (-(lam * k)))) lam := by
    intro k
    have h1 : HasDerivAt (fun t : ℝ => -(t * (k : ℝ))) (-(k : ℝ)) lam := by
      simpa using ((hasDerivAt_id lam).mul_const (k : ℝ)).neg
    have h2 := h1.exp
    convert h2 using 1
    ring
  have h := HasDerivAt.sum (u := D.diffSupport)
    (A := fun (d : ℤ) (t : ℝ) => Real.exp (-(t * (D.kappa d : ℝ))))
    (A' := fun d : ℤ => -((D.kappa d : ℝ) * Real.exp (-(lam * D.kappa d)))) (x := lam)
    (fun d _ => key (D.kappa d))
  rw [Finset.sum_neg_distrib] at h
  have heq : (∑ i ∈ D.diffSupport, (fun (d : ℤ) (t : ℝ) => Real.exp (-(t * (D.kappa d : ℝ)))) i)
      = D.expDiffPartition := by
    funext t
    simp [expDiffPartition, Finset.sum_apply]
  rwa [heq] at h

/-- **The derivative computation of the Remark "The balancing condition at an interior
optimum" (`rem:moment`) of `masked_digit_bound.tex`:**
`F'(λ) = E₊[s] − E₋[κ(d)]`. -/
theorem hasDerivAt_logRatio (lam : ℝ) :
    HasDerivAt D.logRatio (D.meanSumDigit lam - D.meanWitnessCost lam) lam := by
  have hZp := (D.hasDerivAt_expSumPartition lam).log (ne_of_gt (D.expSumPartition_pos lam))
  have hZm := (D.hasDerivAt_expDiffPartition lam).log (ne_of_gt (D.expDiffPartition_pos lam))
  have h := hZm.sub hZp
  have hfun : D.logRatio = fun t => Real.log (D.expDiffPartition t) - Real.log (D.expSumPartition t) := by
    funext t; exact D.logRatio_eq t
  rw [hfun]
  convert h using 1
  rw [meanSumDigit, meanWitnessCost]
  ring

/-- **The balancing condition of the Remark `rem:moment` of `masked_digit_bound.tex`:**
at every interior stationary point of `F(λ) = log P₋(e^{-λ}) − log P₊(e^{-λ})` the mean
weighted sum digit equals the mean minimum difference-witness cost,
`E₊[s] = E₋[κ(d)]`. -/
theorem balancing_of_stationary {lam : ℝ} (h : deriv D.logRatio lam = 0) :
    D.meanSumDigit lam = D.meanWitnessCost lam := by
  have hd := (D.hasDerivAt_logRatio lam).deriv
  rw [h] at hd
  linarith [hd]

end MaskData

end MaskedDigit
