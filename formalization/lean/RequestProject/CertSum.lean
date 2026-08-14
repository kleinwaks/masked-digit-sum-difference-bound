import RequestProject.CertChecks
import RequestProject.CertCheckSum

/-!
# The sum-side certificate of Section 4.3

This file assembles the sum-side half of the controlled-carry certificate of Section 4.3 of
`masked_digit_bound.tex`.

The kernel `CertKernel.Basic` realizes the directed dynamic program of Section 4.1 as a
finite automaton on the canonical base-`q` digits of the *sum*: the state records the
difference `δ` of the two normalized costs of the two carry classes, truncated to
`|δ| ≤ Δ = 60000`.  Its transition rule is the dynamic-programming recursion of Section 4.1,
with the two extreme states used whenever the truncation bites, so that the resulting
automaton *under*-estimates the true costs — which is the admissible direction for an upper
bound on the sum pressure `𝒫₊(x)`.

The main results are

* `sumCert`, the resulting `MaskData.SumCert` for the data of equation (33);
* `PplusPressure_le_log_pCert`: `𝒫₊(x) ≤ log 79.428331`, i.e. the second of the two large
  computational facts of Section 4.3.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

open scoped BigOperators

namespace MaskedDigit

open CertKernel

/-! ## Unfolding lemmas for the kernel's sum automaton -/

theorem scostN_eq (Bp Bq : Array ℕ) (u0 u1 r : ℕ) :
    scostN Bp Bq u0 u1 r = min (sv0 Bp u0 u1 r) (sv1 Bq u0 u1 r) := rfl

theorem snext_eq (Bp Bq : Array ℕ) (u0 u1 r : ℕ) :
    snext Bp Bq u0 u1 r =
      (if INF ≤ sv0 Bp u0 u1 r then 0
       else if INF ≤ sv1 Bq u0 u1 r then 2 * DELS
       else if sv0 Bp u0 u1 r ≤ sv1 Bq u0 u1 r then
         (if DELS < sv1 Bq u0 u1 r - sv0 Bp u0 u1 r then 2 * DELS
          else DELS + (sv1 Bq u0 u1 r - sv0 Bp u0 u1 r))
       else (if DELS < sv0 Bp u0 u1 r - sv1 Bq u0 u1 r then 0
             else DELS - (sv0 Bp u0 u1 r - sv1 Bq u0 u1 r))) := rfl

theorem sterm_eq (Bp Bq m32 e32 V : Array ℕ) (u0 u1 r : ℕ) :
    sterm Bp Bq m32 e32 V u0 u1 r =
      (if INF ≤ scostN Bp Bq u0 u1 r then 0
       else if WSZ ≤ scostN Bp Bq u0 u1 r then (V.getD (snext Bp Bq u0 u1 r) 0) <<< EE
       else ceilShift (m32.getD (scostN Bp Bq u0 u1 r) 0 *
         V.getD (snext Bp Bq u0 u1 r) 0) (e32.getD (scostN Bp Bq u0 u1 r) 0 - EE)) := rfl

/-! ## The two normalized costs of a state -/

theorem su0_of_ge {s : ℕ} (h : DELS ≤ s) : su0 s = 0 := by rw [su0, if_pos h]

theorem su0_of_lt {s : ℕ} (h : s < DELS) : su0 s = DELS - s := by
  rw [su0, if_neg (by omega)]

theorem su1_of_ge {s : ℕ} (h : DELS ≤ s) : su1 s = s - DELS := by rw [su1, if_pos h]

theorem su1_of_lt {s : ℕ} (h : s < DELS) : su1 s = 0 := by rw [su1, if_neg (by omega)]

theorem su0_le (s : ℕ) : su0 s ≤ DELS := by unfold su0; split_ifs <;> omega

theorem su1_le {s : ℕ} (h : s ≤ 2 * DELS) : su1 s ≤ DELS := by
  unfold su1; split_ifs <;> omega

theorem snext_lt (Bp Bq : Array ℕ) (u0 u1 r : ℕ) : snext Bp Bq u0 u1 r < NSS := by
  rw [snext_eq]
  have hD : DELS = 60000 := rfl
  have hN : NSS = 120001 := rfl
  split_ifs <;> omega

theorem snext_le (Bp Bq : Array ℕ) (u0 u1 r : ℕ) : snext Bp Bq u0 u1 r ≤ 2 * DELS := by
  have := snext_lt Bp Bq u0 u1 r
  have hD : DELS = 60000 := rfl
  have hN : NSS = 120001 := rfl
  omega

/-! ## The digit cost tables -/

theorem BpA_eq :
    BpA = tabArr (fun i => if 1 ≤ i && i - 1 ≤ 2 * CertKernel.B &&
      sumArr.getD (i - 1) false then i - 1 else INF) (CertKernel.Q + 2) := rfl

theorem BqA_eq :
    BqA = tabArr (fun i => if i + CertKernel.Q - 1 ≤ 2 * CertKernel.B &&
      sumArr.getD (i + CertKernel.Q - 1) false then i + CertKernel.Q - 1 else INF)
      (CertKernel.Q + 2) := rfl

-- The kernel's tables are large explicit arrays; the elaborator must never try to evaluate
-- them, so they are sealed here.  All access goes through the `getD` lemmas below.
attribute [local irreducible] BpA BqA sumArr maskArr maskList kapArr witArr sumV m32U e32U
  wtArrU

theorem BpA_getD {i : ℕ} (hi : i < CertKernel.Q + 2) :
    BpA.getD i INF = if 1 ≤ i && i - 1 ≤ 2 * CertKernel.B && sumArr.getD (i - 1) false
      then i - 1 else INF := by
  rw [BpA_eq, tabArr_getD _ _ hi]

theorem BqA_getD {i : ℕ} (hi : i < CertKernel.Q + 2) :
    BqA.getD i INF = if i + CertKernel.Q - 1 ≤ 2 * CertKernel.B &&
      sumArr.getD (i + CertKernel.Q - 1) false then i + CertKernel.Q - 1 else INF := by
  rw [BqA_eq, tabArr_getD _ _ hi]

/-- A finite entry of the kernel's `B⁺` table is at most `2B`. -/
theorem BpA_le (i : ℕ) (h : BpA.getD i INF < INF) : BpA.getD i INF ≤ 2 * CertKernel.B := by
  by_cases hi : i < CertKernel.Q + 2
  · rw [BpA_getD hi] at h ⊢
    split_ifs at h ⊢ with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    · exact absurd h (by omega)
  · rw [getD_of_size_le _ _ (by rw [BpA_eq, tabArr_size]; omega)] at h
    exact absurd h (by omega)

/-- A finite entry of the kernel's `B⁻` table is at most `2B`. -/
theorem BqA_le (i : ℕ) (h : BqA.getD i INF < INF) : BqA.getD i INF ≤ 2 * CertKernel.B := by
  by_cases hi : i < CertKernel.Q + 2
  · rw [BqA_getD hi] at h ⊢
    split_ifs at h ⊢ with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      omega
    · exact absurd h (by omega)
  · rw [getD_of_size_le _ _ (by rw [BqA_eq, tabArr_size]; omega)] at h
    exact absurd h (by omega)

/-- **The kernel's `B⁺` table under-estimates the sum-digit cost** of Section 4.1 of
`masked_digit_bound.tex`: entry `i` is a lower bound for the cost of the sum digit
`i - 1`. -/
theorem toE_BpA_le {i : ℕ} (hi : i ≤ CertKernel.Q + 1) :
    toE (BpA.getD i INF) ≤ finalMaskData.scost ((i : ℤ) - 1) := by
  rw [MaskData.scost]
  split_ifs with hc
  · obtain ⟨hnn, hmem⟩ := hc
    have hi1 : 1 ≤ i := by omega
    have hval : ((i : ℤ) - 1).toNat = i - 1 := by omega
    rw [hval] at hmem ⊢
    obtain ⟨b, hb, c, hcM, hbc⟩ := finalMaskData.mem_sumSupport.1 hmem
    have hsum : sumArr.getD (i - 1) false = true := by
      rw [← hbc]; exact sumArr_of_mem hb hcM
    have hle : i - 1 ≤ 2 * CertKernel.B := by
      have := finalMaskData.le_of_mem_sumSupport hmem
      have hB : finalMaskData.B = CertKernel.B := finalMaskData_B.trans certB_eq.symm
      omega
    rw [BpA_getD (by omega), if_pos (by simp [hi1, hle, hsum]),
      toE_of_lt (by simp only [CertKernel.B, INF] at hle ⊢; omega)]
  · exact le_top

/-- **The kernel's `B⁻` table under-estimates the sum-digit cost**: entry `i` is a lower
bound for the cost of the sum digit `i - 1 + q`. -/
theorem toE_BqA_le {i : ℕ} (hi : i ≤ CertKernel.Q + 1) :
    toE (BqA.getD i INF) ≤ finalMaskData.scost ((i : ℤ) - 1 + (CertKernel.Q : ℤ)) := by
  have hQ : CertKernel.Q = 27022 := rfl
  rw [MaskData.scost]
  split_ifs with hc
  · obtain ⟨hnn, hmem⟩ := hc
    have hval : ((i : ℤ) - 1 + (CertKernel.Q : ℤ)).toNat = i + CertKernel.Q - 1 := by
      simp only [hQ] at *
      omega
    rw [hval] at hmem ⊢
    obtain ⟨b, hb, c, hcM, hbc⟩ := finalMaskData.mem_sumSupport.1 hmem
    have hsum : sumArr.getD (i + CertKernel.Q - 1) false = true := by
      rw [← hbc]; exact sumArr_of_mem hb hcM
    have hle : i + CertKernel.Q - 1 ≤ 2 * CertKernel.B := by
      have := finalMaskData.le_of_mem_sumSupport hmem
      have hB : finalMaskData.B = CertKernel.B := finalMaskData_B.trans certB_eq.symm
      omega
    rw [BqA_getD (by omega), if_pos (by simp [hle, hsum]),
      toE_of_lt (by simp only [CertKernel.B, INF] at hle ⊢; omega)]
  · exact le_top

/-! ## The soundness of the transition rule -/

/-- Adding two finite kernel costs. -/
theorem toE_add_eq {a b : ℕ} (h : a + b < INF) : toE a + toE b = toE (a + b) :=
  le_antisymm (toE_add_le a b) (toE_le_add (fun _ _ => h))

/-- The outgoing-carry-`0` half of the transition rule, as pure arithmetic on the two new
costs. -/
theorem cost_add_su0_le (v0 v1 : ℕ) :
    toE (min v0 v1) +
      toE (su0 (if INF ≤ v0 then 0
        else if INF ≤ v1 then 2 * DELS
        else if v0 ≤ v1 then (if DELS < v1 - v0 then 2 * DELS else DELS + (v1 - v0))
        else (if DELS < v0 - v1 then 0 else DELS - (v0 - v1)))) ≤ toE v0 := by
  split_ifs with h0 h1 h2 h3 h4
  · rw [toE_of_ge h0]; exact le_top
  · rw [su0_of_ge (by omega : DELS ≤ 2 * DELS), toE_zero, add_zero,
      min_eq_left (by omega : v0 ≤ v1)]
  · rw [su0_of_ge (by omega : DELS ≤ 2 * DELS), toE_zero, add_zero, min_eq_left h2]
  · rw [su0_of_ge (by omega : DELS ≤ DELS + (v1 - v0)), toE_zero, add_zero, min_eq_left h2]
  · rw [su0_of_lt (by simp only [DELS]; omega : 0 < DELS), Nat.sub_zero,
      min_eq_right (by omega : v1 ≤ v0),
      toE_add_eq (by simp only [INF, DELS] at *; omega)]
    exact toE_mono (by omega)
  · rw [su0_of_lt (by omega : DELS - (v0 - v1) < DELS),
      show DELS - (DELS - (v0 - v1)) = v0 - v1 from by omega,
      min_eq_right (by omega : v1 ≤ v0),
      toE_add_eq (by omega : v1 + (v0 - v1) < INF),
      show v1 + (v0 - v1) = v0 from by omega]

/-- The outgoing-carry-`1` half of the transition rule, as pure arithmetic on the two new
costs. -/
theorem cost_add_su1_le (v0 v1 : ℕ) :
    toE (min v0 v1) +
      toE (su1 (if INF ≤ v0 then 0
        else if INF ≤ v1 then 2 * DELS
        else if v0 ≤ v1 then (if DELS < v1 - v0 then 2 * DELS else DELS + (v1 - v0))
        else (if DELS < v0 - v1 then 0 else DELS - (v0 - v1)))) ≤ toE v1 := by
  split_ifs with h0 h1 h2 h3 h4
  · rw [su1_of_lt (by simp only [DELS]; omega : 0 < DELS), toE_zero, add_zero]
    exact toE_mono (min_le_right _ _)
  · rw [toE_of_ge h1]; exact le_top
  · rw [su1_of_ge (by omega : DELS ≤ 2 * DELS),
      show 2 * DELS - DELS = DELS from by omega, min_eq_left h2,
      toE_add_eq (by simp only [INF, DELS] at *; omega)]
    exact toE_mono (by omega)
  · rw [su1_of_ge (by omega : DELS ≤ DELS + (v1 - v0)),
      show DELS + (v1 - v0) - DELS = v1 - v0 from by omega, min_eq_left h2,
      toE_add_eq (by omega : v0 + (v1 - v0) < INF),
      show v0 + (v1 - v0) = v1 from by omega]
  · rw [su1_of_lt (by simp only [DELS]; omega : 0 < DELS), toE_zero, add_zero,
      min_eq_right (by omega : v1 ≤ v0)]
  · rw [su1_of_lt (by omega : DELS - (v0 - v1) < DELS), toE_zero, add_zero,
      min_eq_right (by omega : v1 ≤ v0)]

/-- The outgoing-carry-`0` soundness condition of the kernel's sum automaton, stated for
arbitrary cost tables so that the two large tables of the kernel are never unfolded. -/
theorem sumCert_sound0_gen (Bp Bq : Array ℕ) (a b : ℕ∞) (u0 u1 r : ℕ)
    (hu0 : u0 ≤ DELS) (hu1 : u1 ≤ DELS)
    (hBp : ∀ i, Bp.getD i INF < INF → Bp.getD i INF ≤ 2 * CertKernel.B)
    (ha : toE (Bp.getD (r + 1) INF) ≤ a) (hb : toE (Bp.getD r INF) ≤ b) :
    toE (scostN Bp Bq u0 u1 r) + toE (su0 (snext Bp Bq u0 u1 r))
      ≤ min (toE u0 + a) (toE u1 + b) := by
  have hkey : toE (scostN Bp Bq u0 u1 r) + toE (su0 (snext Bp Bq u0 u1 r))
      ≤ toE (sv0 Bp u0 u1 r) := by
    rw [scostN_eq, snext_eq]
    exact cost_add_su0_le _ _
  refine le_trans hkey ?_
  rw [sv0, toE_min]
  refine min_le_min ?_ ?_
  · refine le_trans (toE_le_add ?_) (add_le_add (le_refl _) ha)
    intro _ hlt
    have := hBp (r + 1) hlt
    simp only [CertKernel.B, DELS, INF] at *
    omega
  · refine le_trans (toE_le_add ?_) (add_le_add (le_refl _) hb)
    intro _ hlt
    have := hBp r hlt
    simp only [CertKernel.B, DELS, INF] at *
    omega

/-- The outgoing-carry-`1` soundness condition of the kernel's sum automaton, stated for
arbitrary cost tables. -/
theorem sumCert_sound1_gen (Bp Bq : Array ℕ) (a b : ℕ∞) (u0 u1 r : ℕ)
    (hu0 : u0 ≤ DELS) (hu1 : u1 ≤ DELS)
    (hBq : ∀ i, Bq.getD i INF < INF → Bq.getD i INF ≤ 2 * CertKernel.B)
    (ha : toE (Bq.getD (r + 1) INF) ≤ a) (hb : toE (Bq.getD r INF) ≤ b) :
    toE (scostN Bp Bq u0 u1 r) + toE (su1 (snext Bp Bq u0 u1 r))
      ≤ min (toE u0 + a) (toE u1 + b) := by
  have hkey : toE (scostN Bp Bq u0 u1 r) + toE (su1 (snext Bp Bq u0 u1 r))
      ≤ toE (sv1 Bq u0 u1 r) := by
    rw [scostN_eq, snext_eq]
    exact cost_add_su1_le _ _
  refine le_trans hkey ?_
  rw [sv1, toE_min]
  refine min_le_min ?_ ?_
  · refine le_trans (toE_le_add ?_) (add_le_add (le_refl _) ha)
    intro _ hlt
    have := hBq (r + 1) hlt
    simp only [CertKernel.B, DELS, INF] at *
    omega
  · refine le_trans (toE_le_add ?_) (add_le_add (le_refl _) hb)
    intro _ hlt
    have := hBq r hlt
    simp only [CertKernel.B, DELS, INF] at *
    omega

/-! ## The certificate -/

theorem finalQ_eq : finalMaskData.q = CertKernel.Q := finalMaskData_q.trans certQ_eq.symm

/-- The outgoing-carry-`0` soundness condition of the kernel's sum automaton: the relaxed
first line of the dynamic-programming recursion of Section 4.1 of
`masked_digit_bound.tex`. -/
theorem sumCert_sound0 {u0 u1 r : ℕ} (hu0 : u0 ≤ DELS) (hu1 : u1 ≤ DELS)
    (hr : r < finalMaskData.q) :
    toE (scostN BpA BqA u0 u1 r) + toE (su0 (snext BpA BqA u0 u1 r))
      ≤ min (toE u0 + finalMaskData.scost (r : ℤ))
          (toE u1 + finalMaskData.scost ((r : ℤ) - 1)) := by
  rw [finalQ_eq] at hr
  refine sumCert_sound0_gen BpA BqA _ _ u0 u1 r hu0 hu1 BpA_le ?_ (toE_BpA_le (by omega))
  have h := toE_BpA_le (i := r + 1) (by omega)
  rwa [show ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) from by push_cast; ring] at h

/-- The outgoing-carry-`1` soundness condition of the kernel's sum automaton: the relaxed
second line of the dynamic-programming recursion of Section 4.1 of
`masked_digit_bound.tex`. -/
theorem sumCert_sound1 {u0 u1 r : ℕ} (hu0 : u0 ≤ DELS) (hu1 : u1 ≤ DELS)
    (hr : r < finalMaskData.q) :
    toE (scostN BpA BqA u0 u1 r) + toE (su1 (snext BpA BqA u0 u1 r))
      ≤ min (toE u0 + finalMaskData.scost ((r : ℤ) + (finalMaskData.q : ℤ)))
          (toE u1 + finalMaskData.scost ((r : ℤ) + (finalMaskData.q : ℤ) - 1)) := by
  have hq : (finalMaskData.q : ℤ) = (CertKernel.Q : ℤ) := by rw [finalQ_eq]
  rw [finalQ_eq] at hr
  refine sumCert_sound1_gen BpA BqA _ _ u0 u1 r hu0 hu1 BqA_le ?_ ?_
  · have h := toE_BqA_le (i := r + 1) (by omega)
    rw [show ((r + 1 : ℕ) : ℤ) - 1 + (CertKernel.Q : ℤ) = (r : ℤ) + (CertKernel.Q : ℤ) from by
      push_cast; ring] at h
    rwa [hq]
  · have h := toE_BqA_le (i := r) (by omega)
    rw [show (r : ℤ) - 1 + (CertKernel.Q : ℤ) = (r : ℤ) + (CertKernel.Q : ℤ) - 1 from by
      ring] at h
    rwa [hq]

/-- **The sum-side finite carry certificate** of Section 4.3 of `masked_digit_bound.tex`, as
computed by the kernel: the truncated carry graph of the directed dynamic program of
Section 4.1 with `|δ| ≤ 60000`. -/
noncomputable def sumCert : finalMaskData.SumCert where
  n := NSS
  u0 := fun s => toE (su0 (s : ℕ))
  u1 := fun s => toE (su1 (s : ℕ))
  next := fun s r => ⟨snext BpA BqA (su0 (s : ℕ)) (su1 (s : ℕ)) r, snext_lt _ _ _ _ _⟩
  cost := fun s r => toE (scostN BpA BqA (su0 (s : ℕ)) (su1 (s : ℕ)) r)
  start := ⟨DELS, by norm_num [NSS, DELS]⟩
  u0_start := by
    show toE (su0 DELS) = 0
    rw [su0_of_ge (le_refl _), toE_zero]
  sound0 := by
    intro s r hr
    have hs : (s : ℕ) ≤ 2 * DELS := by
      have := s.isLt
      simp only [NSS, DELS] at *
      omega
    exact sumCert_sound0 (su0_le (s : ℕ)) (su1_le hs) hr
  sound1 := by
    intro s r hr
    have hs : (s : ℕ) ≤ 2 * DELS := by
      have := s.isLt
      simp only [NSS, DELS] at *
      omega
    exact sumCert_sound1 (su0_le (s : ℕ)) (su1_le hs) hr

/-! ## The row sums -/

/-- **Each term of a sum-side row sum is an upper bound for the corresponding term of the
Collatz--Wielandt sum**, in units of `2 ^ EE`. -/
theorem le_sterm_real (u0 u1 r : ℕ) :
    2 ^ EE * (epow xR (toE (scostN BpA BqA u0 u1 r)) *
        ((sumV.getD (snext BpA BqA u0 u1 r) 0 : ℕ) : ℝ))
      ≤ ((sterm BpA BqA m32U e32U sumV u0 u1 r : ℕ) : ℝ) := by
  rw [sterm_eq, epow_toE]
  set a := scostN BpA BqA u0 u1 r with ha
  set ns := snext BpA BqA u0 u1 r with hns
  set V := (sumV.getD ns 0 : ℕ) with hV
  have hVnn : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg _
  split_ifs with h hW
  · simp
  · -- the cost is too large for the weight table: use `x ^ a ≤ 1`
    have hx : xR ^ a ≤ 1 := pow_le_one₀ xR_pos.le xR_le_one
    have hcast : (((V <<< EE : ℕ)) : ℝ) = (V : ℝ) * 2 ^ EE := by
      rw [Nat.shiftLeft_eq]; push_cast; ring
    rw [hcast]
    have : xR ^ a * (V : ℝ) ≤ (V : ℝ) := by nlinarith [pow_nonneg xR_pos.le a]
    nlinarith [this]
  · have haW : a ≤ WSZ := by omega
    have hEE : EE ≤ e32U.getD a 0 := EE_le_e32U haW
    have hm := le_m32U haW
    set e := e32U.getD a 0 with he
    set m := m32U.getD a 0 with hm'
    refine le_trans ?_ (le_cast_ceilShift (m * V) (e - EE))
    have hcast : (((m * V : ℕ)) : ℝ) = (m : ℝ) * (V : ℝ) := by push_cast; ring
    rw [hcast, le_div_iff₀ (by positivity)]
    have hsplit : (2 : ℝ) ^ e = 2 ^ (e - EE) * 2 ^ EE := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 ^ EE * (xR ^ a * (V : ℝ)) * 2 ^ (e - EE)
        = (xR ^ a * 2 ^ e) * (V : ℝ) := by rw [hsplit]; ring
      _ ≤ (m : ℝ) * (V : ℝ) := mul_le_mul_of_nonneg_right hm hVnn

theorem srowAux_eq (Bp Bq m32 e32 V : Array ℕ) (u0 u1 : ℕ) :
    ∀ (m : ℕ) (acc : ℕ), srowAux Bp Bq m32 e32 V u0 u1 m acc =
      acc + ∑ r ∈ Finset.range m, sterm Bp Bq m32 e32 V u0 u1 r := by
  intro m
  induction m with
  | zero => intro acc; simp [srowAux]
  | succ k ih =>
      intro acc
      rw [srowAux, ih, Finset.sum_range_succ]
      omega

theorem srow_eq (s : ℕ) :
    srow BpA BqA m32U e32U sumV s =
      ∑ r ∈ Finset.range CertKernel.Q,
        sterm BpA BqA m32U e32U sumV (su0 s) (su1 s) r := by
  rw [srow, srowAux_eq]
  omega

/-! ## The Collatz--Wielandt inequality -/

/-- The certificate vector, as a positive real vector on the states. -/
noncomputable def sumVR : Fin sumCert.n → ℝ := fun s => ((sumV.getD (s : ℕ) 0 : ℕ) : ℝ)

theorem sumVR_pos (s : Fin sumCert.n) : 0 < sumVR s := by
  have h := allB_spec sumVPos_true (s : ℕ) s.isLt
  simp only [decide_eq_true_eq] at h
  rw [sumVR]
  exact_mod_cast h

theorem sumCert_cw (s : Fin sumCert.n) :
    ∑ r : Fin finalMaskData.q, epow xR (sumCert.cost s r) * sumVR (sumCert.next s r)
      ≤ (pCert : ℝ) * sumVR s := by
  have hq : finalMaskData.q = CertKernel.Q := finalQ_eq
  -- the row sum bounds the Collatz--Wielandt sum from above
  have hsum : 2 ^ EE * ∑ r : Fin finalMaskData.q,
        epow xR (sumCert.cost s r) * sumVR (sumCert.next s r)
      ≤ ((srow BpA BqA m32U e32U sumV (s : ℕ) : ℕ) : ℝ) := by
    rw [srow_eq]
    rw [Fin.sum_univ_eq_sum_range
      (fun r => epow xR (sumCert.cost s r) * sumVR (sumCert.next s r)) finalMaskData.q, hq,
      Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    exact le_sterm_real _ _ r
  -- the evaluated test
  have htest := allB_spec sumRowCheck_true (s : ℕ) s.isLt
  rw [stest, decide_eq_true_eq, Nat.shiftLeft_eq] at htest
  have htestR : (pDen : ℝ) * ((srow BpA BqA m32U e32U sumV (s : ℕ) : ℕ) : ℝ)
      ≤ (pNum : ℝ) * ((sumV.getD (s : ℕ) 0 : ℕ) : ℝ) * 2 ^ EE := by
    have := (Nat.cast_le (α := ℝ)).2 htest
    push_cast at this
    linarith
  have hEEpos : (0 : ℝ) < 2 ^ EE := by positivity
  have hpNum : ((pNum : ℕ) : ℝ) = 79428331 := by norm_num [pNum]
  have hpDen : ((pDen : ℕ) : ℝ) = 1000000 := by norm_num [pDen]
  have hpCert : (pCert : ℝ) = 79428331 / 1000000 := by rw [pCert]; norm_num
  set S := ∑ r : Fin finalMaskData.q,
    epow xR (sumCert.cost s r) * sumVR (sumCert.next s r) with hS
  rw [hpNum, hpDen] at htestR
  rw [hpCert]
  have hVs : sumVR s = ((sumV.getD (s : ℕ) 0 : ℕ) : ℝ) := rfl
  have hchain : (1000000 : ℝ) * (2 ^ EE * S) ≤ 79428331 * sumVR s * 2 ^ EE := by
    rw [hVs]
    calc (1000000 : ℝ) * (2 ^ EE * S)
        ≤ 1000000 * ((srow BpA BqA m32U e32U sumV (s : ℕ) : ℕ) : ℝ) := by linarith
      _ ≤ 79428331 * ((sumV.getD (s : ℕ) 0 : ℕ) : ℝ) * 2 ^ EE := htestR
  have hkey : (1000000 * S) * 2 ^ EE ≤ (79428331 * sumVR s) * 2 ^ EE := by linarith
  have := le_of_mul_le_mul_right hkey hEEpos
  linarith

/-- **The sum-side certificate of Section 4.3 of `masked_digit_bound.tex`:**
`𝒫₊(x) ≤ log 79.428331`. -/
theorem PplusPressure_le_log_pCert :
    finalMaskData.PplusPressure xR ≤ Real.log (pCert : ℝ) :=
  sumCert.PplusPressure_le_log xR_pos xR_lt_one sumVR (pCert : ℝ) (by norm_num [pCert])
    sumVR_pos sumCert_cw

end MaskedDigit
