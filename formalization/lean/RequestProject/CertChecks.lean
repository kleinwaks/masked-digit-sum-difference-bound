import RequestProject.CertWeights
import RequestProject.FinalData

/-!
# The discrete checks of the certificate kernel

The kernel `CertKernel.Basic` rebuilds, from the six generators of equation (33)
(`eq:controlled-mask`) of `masked_digit_bound.tex`, the mask `M`, the table of witness costs
`κ` of equation (3) (`eq:kappa`) and the sum support `S = M + M`.  This file checks by
evaluation that these tables are correct in the only two directions that the certificate
needs:

* every finite entry of the kernel's `κ`-table is realized by a genuine pair of mask
  elements, so that the kernel's difference costs are an *upper* bound for `w = κ`;
* every sum of two mask elements is recorded in the kernel's sum-support table, so that the
  kernel's sum costs are a *lower* bound for the true digit costs.

These are exactly the two soundness directions required by `MaskData.DiffCert` and
`MaskData.SumCert`.
-/

open scoped BigOperators

namespace MaskedDigit

open CertKernel

/-! ## A generic array lemma -/

theorem getD_of_size_le {α : Type _} (a : Array α) (d : α) {i : ℕ} (h : a.size ≤ i) :
    a.getD i d = d := by
  simp [Array.getD, Nat.not_lt.2 h]

/-! ## The mask -/

theorem maskStep_eq : maskStep = semiStep finalGeneratorsList := rfl

theorem certB_eq : CertKernel.B = finalB := rfl

theorem certQ_eq : CertKernel.Q = finalQ := rfl

theorem maskArr_eq : maskArr = semiArr finalGeneratorsList finalB := by
  unfold maskArr semiArr
  rw [maskStep_eq, certB_eq]

/-- The kernel's membership table is the mask `M` of equation (33) of
`masked_digit_bound.tex`. -/
theorem maskArr_getD_iff (v : ℕ) : maskArr.getD v false = true ↔ v ∈ finalMaskData.M := by
  rw [maskArr_eq, semiArr_getD_iff_mem,
    finalMaskData_M,
    mem_generatedUpTo, finalGenerators_coe]

theorem mem_maskList_iff (v : ℕ) : v ∈ maskList ↔ v ∈ finalMaskData.M := by
  rw [maskList, maskListOf]
  simp only [List.mem_filter, List.mem_range]
  rw [show ((maskArr.getD v false) = true) ↔ v ∈ finalMaskData.M from maskArr_getD_iff v]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    have hle := finalMaskData.digits_le v h
    have hB : finalMaskData.B = finalB := finalMaskData_B
    have hB2 : CertKernel.B = finalB := certB_eq
    exact ⟨by omega, h⟩

/-- Every mask element is at most `B`. -/
theorem mem_maskList_le {v : ℕ} (h : v ∈ maskList) : v ≤ CertKernel.B := by
  rw [certB_eq, ← finalMaskData_B]
  exact finalMaskData.digits_le v ((mem_maskList_iff v).1 h)

/-! ## The two evaluated checks -/

/-- Every finite entry of the kernel's witness-cost table is realized by a genuine pair of
mask elements. -/
theorem kapCheck_true : kapCheck () = true := by native_decide

/-- The kernel's sum-support table contains every sum of two mask elements. -/
theorem sumCheck_true : sumCheck () = true := by native_decide

/-! ## Their consequences -/

/-- **Soundness of the kernel's witness costs.**  A finite entry `kapArr[d]` is the cost
`b + (b + d)` of a genuine pair of mask elements with difference `d`; in particular
`κ(d) ≤ kapArr[d]` and `d ∈ M - M`. -/
theorem kapArr_spec {d : ℕ} (hd : d ≤ CertKernel.B) (h : kapArr.getD d INF < INF) :
    ∃ b, b ∈ finalMaskData.M ∧ b + d ∈ finalMaskData.M ∧
      kapArr.getD d INF = 2 * b + d := by
  have hall := allB_spec kapCheck_true d (by omega)
  set k := kapArr.getD d INF with hk
  set b := witArr.getD d 0 with hb
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hall
  rcases hall with heq | ⟨⟨⟨h1, -⟩, h3⟩, h4⟩
  · omega
  · exact ⟨b, (maskArr_getD_iff b).1 h1, (maskArr_getD_iff _).1 h3, h4⟩

/-- **Soundness of the kernel's sum-support table**: it contains the whole of `S = M + M`. -/
theorem sumArr_of_mem {b c : ℕ} (hb : b ∈ finalMaskData.M) (hc : c ∈ finalMaskData.M) :
    sumArr.getD (b + c) false = true := by
  have h := sumCheck_true
  rw [sumCheck] at h
  simp only [List.all_eq_true] at h
  exact h b ((mem_maskList_iff b).2 hb) c ((mem_maskList_iff c).2 hc)

end MaskedDigit
