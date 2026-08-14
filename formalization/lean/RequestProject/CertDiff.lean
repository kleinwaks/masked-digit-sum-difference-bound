import RequestProject.CertChecks
import RequestProject.CertCheckDiff

/-!
# The difference-side certificate of Section 4.3

This file assembles the difference-side half of the controlled-carry certificate of
Section 4.3 of `masked_digit_bound.tex`.

The kernel `CertKernel.Basic` realizes the truncated carry graph of Section 4.2 as a finite
automaton on the canonical base-`q` digits: the state records the difference `δ` of the two
normalized costs `(C^{(0)}, C^{(1)})` defined immediately before equation (29), truncated
to `|δ| ≤ Δ = 32000` and
completed by the two states `δ = ±∞`.  Its transition rule is the one of equation (29)
(`eq:carry-transition`), with the two extreme states used whenever the truncation bites, so
that the resulting automaton *over*-estimates the true costs — which is the admissible
direction for a lower bound on the difference pressure `𝒫₋(x)`.

The main results are

* `diffCert`, the resulting `MaskData.DiffCert` for the data of equation (33);
* `log_cCert_le_PminusPressure`: `log 582.117820 ≤ 𝒫₋(x)`, i.e. the first of the two large
  computational facts of Section 4.3.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

open scoped BigOperators

namespace MaskedDigit

open CertKernel

/-! ## Unfolding lemmas for the kernel's difference automaton -/

theorem dcost_eq (Ap Am : Array ℕ) (u0 u1 r : ℕ) :
    dcost Ap Am u0 u1 r = min (dv0 Ap u0 u1 r) (dv1 Am u0 u1 r) := rfl

theorem dnext_eq (Ap Am : Array ℕ) (u0 u1 r : ℕ) :
    dnext Ap Am u0 u1 r =
      (if INF ≤ dv0 Ap u0 u1 r then NIDXD
       else if INF ≤ dv1 Am u0 u1 r then PIDXD
       else if dv0 Ap u0 u1 r ≤ dv1 Am u0 u1 r then
         (if DELD < dv1 Am u0 u1 r - dv0 Ap u0 u1 r then PIDXD
          else DELD + (dv1 Am u0 u1 r - dv0 Ap u0 u1 r))
       else (if DELD < dv0 Ap u0 u1 r - dv1 Am u0 u1 r then NIDXD
             else DELD - (dv0 Ap u0 u1 r - dv1 Am u0 u1 r))) := rfl

theorem dterm_eq (Ap Am m32 e32 V : Array ℕ) (u0 u1 r : ℕ) :
    dterm Ap Am m32 e32 V u0 u1 r =
      if INF ≤ dcost Ap Am u0 u1 r then 0
      else (m32.getD (dcost Ap Am u0 u1 r) 0 * V.getD (dnext Ap Am u0 u1 r) 0) >>>
        (e32.getD (dcost Ap Am u0 u1 r) 0 - EE) := rfl

/-! ## The two normalized costs of a state -/

theorem du0_of_lt {s : ℕ} (h : s < DELD) : du0 s = DELD - s := by
  rw [du0, if_pos (by omega : s ≤ 2 * DELD), if_neg (by omega : ¬ DELD ≤ s)]

theorem du0_of_ge {s : ℕ} (h : DELD ≤ s) (h2 : s ≤ 2 * DELD) : du0 s = 0 := by
  rw [du0, if_pos h2, if_pos h]

theorem du1_of_lt {s : ℕ} (h : s < DELD) : du1 s = 0 := by
  rw [du1, if_pos (by omega : s ≤ 2 * DELD), if_neg (by omega : ¬ DELD ≤ s)]

theorem du1_of_ge {s : ℕ} (h : DELD ≤ s) (h2 : s ≤ 2 * DELD) : du1 s = s - DELD := by
  rw [du1, if_pos h2, if_pos h]

theorem du0_NIDXD : du0 NIDXD = INF := by decide

theorem du0_PIDXD : du0 PIDXD = 0 := by decide

theorem du1_NIDXD : du1 NIDXD = 0 := by decide

theorem du1_PIDXD : du1 PIDXD = INF := by decide

theorem du0_bound (s : ℕ) : du0 s ≤ DELD ∨ du0 s = INF := by
  unfold du0; split_ifs <;> omega

theorem du1_bound (s : ℕ) : du1 s ≤ DELD ∨ du1 s = INF := by
  unfold du1; split_ifs <;> omega

/-! ## The digit cost tables -/

/-- The extended digit cost of Section 4.2 of `masked_digit_bound.tex` at a difference digit
is the witness cost `κ` of equation (3). -/
theorem wcost_eq_kappa (D : MaskData) {d : ℤ} (hd : d ∈ D.diffSupport) :
    D.wcost d = (D.kappa d : ℕ∞) := by
  rw [MaskData.wcost, if_pos hd]


theorem ApA_eq :
    ApA = tabArr (fun r => if r ≤ CertKernel.B then kapArr.getD r INF else INF)
      (CertKernel.Q + 2) := rfl

theorem AmA_eq :
    AmA = tabArr
      (fun r => if r ≤ CertKernel.Q && CertKernel.Q - r ≤ CertKernel.B
        then kapArr.getD (CertKernel.Q - r) INF else INF) (CertKernel.Q + 2) := rfl

-- The kernel's tables are large explicit arrays; the elaborator must never try to evaluate
-- them, so they are sealed here.  All access goes through the `getD` lemmas below.
attribute [local irreducible] ApA AmA kapArr witArr maskArr maskList diffV m32L e32L
  wtArr

theorem ApA_getD (r : ℕ) :
    ApA.getD r INF = if r ≤ CertKernel.B then kapArr.getD r INF else INF := by
  by_cases h : r < CertKernel.Q + 2
  · rw [ApA_eq, tabArr_getD _ _ h]
  · rw [ApA_eq, getD_of_size_le _ _ (by rw [tabArr_size]; omega),
      if_neg (by simp only [CertKernel.B, CertKernel.Q] at *; omega)]

theorem AmA_getD (r : ℕ) :
    AmA.getD r INF =
      if r ≤ CertKernel.Q && CertKernel.Q - r ≤ CertKernel.B
        then kapArr.getD (CertKernel.Q - r) INF else INF := by
  by_cases h : r < CertKernel.Q + 2
  · rw [AmA_eq, tabArr_getD _ _ h]
  · rw [AmA_eq, getD_of_size_le _ _ (by rw [tabArr_size]; omega),
      if_neg (by simp only [Bool.and_eq_true, decide_eq_true_eq, CertKernel.Q] at *; omega)]

/-- A finite entry of the kernel's witness-cost table is at most `2B`. -/
theorem kapArr_le {d : ℕ} (hd : d ≤ CertKernel.B) (h : kapArr.getD d INF < INF) :
    kapArr.getD d INF ≤ 2 * CertKernel.B := by
  obtain ⟨b, hbM, hbdM, hval⟩ := kapArr_spec hd h
  have h1 := finalMaskData.digits_le b hbM
  have h2 := finalMaskData.digits_le (b + d) hbdM
  have hB : finalMaskData.B = CertKernel.B := finalMaskData_B.trans certB_eq.symm
  omega

theorem ApA_le {r : ℕ} (h : ApA.getD r INF < INF) : ApA.getD r INF ≤ 2 * CertKernel.B := by
  rw [ApA_getD] at h ⊢
  split_ifs at h ⊢ with hr
  · exact kapArr_le hr h
  · exact absurd h (by omega)

theorem AmA_le {r : ℕ} (h : AmA.getD r INF < INF) : AmA.getD r INF ≤ 2 * CertKernel.B := by
  rw [AmA_getD] at h ⊢
  split_ifs at h ⊢ with hr
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact kapArr_le hr.2 h
  · exact absurd h (by omega)

/-- **The kernel's `A⁺` table over-estimates the extended digit cost `w`** of Section 4.2 of
`masked_digit_bound.tex`. -/
theorem wcost_le_ApA (r : ℕ) : finalMaskData.wcost (r : ℤ) ≤ toE (ApA.getD r INF) := by
  rw [ApA_getD]
  split_ifs with hr
  · by_cases hk : kapArr.getD r INF < INF
    · obtain ⟨b, hbM, hbrM, hval⟩ := kapArr_spec hr hk
      have hd : (r : ℤ) ∈ finalMaskData.diffSupport := by
        rw [MaskData.mem_diffSupport]
        exact ⟨b + r, hbrM, b, hbM, by push_cast; ring⟩
      have hkap : finalMaskData.kappa (r : ℤ) ≤ (b + r) + b :=
        finalMaskData.kappa_le hbrM hbM (by push_cast; ring)
      rw [wcost_eq_kappa finalMaskData hd, toE_of_lt hk, hval]
      exact_mod_cast (by omega : finalMaskData.kappa (r : ℤ) ≤ 2 * b + r)
    · rw [toE_of_ge (by omega)]; exact le_top
  · rw [toE_of_ge (le_refl INF)]; exact le_top

/-- **The kernel's `A⁻` table over-estimates the extended digit cost `w`** of the negative
digits. -/
theorem wcost_le_AmA (r : ℕ) :
    finalMaskData.wcost ((r : ℤ) - (finalMaskData.q : ℤ)) ≤ toE (AmA.getD r INF) := by
  rw [AmA_getD]
  have hq : (finalMaskData.q : ℕ) = CertKernel.Q := finalMaskData_q.trans certQ_eq.symm
  split_ifs with hr
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    obtain ⟨hrq, hdB⟩ := hr
    set d := CertKernel.Q - r with hd
    by_cases hk : kapArr.getD d INF < INF
    · obtain ⟨b, hbM, hbdM, hval⟩ := kapArr_spec hdB hk
      have hcast : (r : ℤ) - (finalMaskData.q : ℤ) = (b : ℤ) - ((b + d : ℕ) : ℤ) := by
        rw [hq]
        have : (d : ℤ) = (CertKernel.Q : ℤ) - (r : ℤ) := by
          rw [hd]; push_cast [Nat.cast_sub hrq]; ring
        push_cast at this ⊢
        omega
      have hmem : (r : ℤ) - (finalMaskData.q : ℤ) ∈ finalMaskData.diffSupport := by
        rw [MaskData.mem_diffSupport]
        exact ⟨b, hbM, b + d, hbdM, hcast.symm⟩
      have hkap : finalMaskData.kappa ((r : ℤ) - (finalMaskData.q : ℤ)) ≤ b + (b + d) :=
        finalMaskData.kappa_le hbM hbdM hcast.symm
      rw [wcost_eq_kappa finalMaskData hmem, toE_of_lt hk, hval]
      exact_mod_cast (by omega : finalMaskData.kappa ((r : ℤ) - (finalMaskData.q : ℤ))
        ≤ 2 * b + d)
    · rw [toE_of_ge (by omega)]; exact le_top
  · rw [toE_of_ge (le_refl INF)]; exact le_top

/-! ## The soundness of the transition rule -/

theorem dnext_lt (Ap Am : Array ℕ) (u0 u1 r : ℕ) : dnext Ap Am u0 u1 r < NSD := by
  rw [dnext_eq]
  have hD : DELD = 32000 := rfl
  have hN : NSD = 64003 := rfl
  have hNI : NIDXD = 64001 := rfl
  have hPI : PIDXD = 64002 := rfl
  split_ifs <;> omega

/-- The carry-`0` half of the transition rule, as pure arithmetic on the two new costs. -/
theorem toE_le_cost_add_du0 (v0 v1 : ℕ) :
    toE v0 ≤ toE (min v0 v1) +
      toE (du0 (if INF ≤ v0 then NIDXD
        else if INF ≤ v1 then PIDXD
        else if v0 ≤ v1 then (if DELD < v1 - v0 then PIDXD else DELD + (v1 - v0))
        else (if DELD < v0 - v1 then NIDXD else DELD - (v0 - v1)))) := by
  split_ifs with h0 h1 h2 h3 h4
  · rw [du0_NIDXD, toE_of_ge (le_refl INF)]
    simp
  · rw [du0_PIDXD, toE_zero, add_zero, min_eq_left (by omega : v0 ≤ v1)]
  · rw [du0_PIDXD, toE_zero, add_zero, min_eq_left h2]
  · rw [du0_of_ge (by omega) (by omega), toE_zero, add_zero, min_eq_left h2]
  · rw [du0_NIDXD, toE_of_ge (le_refl INF)]
    simp
  · rw [du0_of_lt (by omega : DELD - (v0 - v1) < DELD), min_eq_right (by omega : v1 ≤ v0),
      show DELD - (DELD - (v0 - v1)) = v0 - v1 from by omega]
    have h := toE_le_add (a := v1) (b := v0 - v1) (by intro _ _; omega)
    rwa [show v1 + (v0 - v1) = v0 from by omega] at h

/-- The carry-`1` half of the transition rule, as pure arithmetic on the two new costs. -/
theorem toE_le_cost_add_du1 (v0 v1 : ℕ) :
    toE v1 ≤ toE (min v0 v1) +
      toE (du1 (if INF ≤ v0 then NIDXD
        else if INF ≤ v1 then PIDXD
        else if v0 ≤ v1 then (if DELD < v1 - v0 then PIDXD else DELD + (v1 - v0))
        else (if DELD < v0 - v1 then NIDXD else DELD - (v0 - v1)))) := by
  split_ifs with h0 h1 h2 h3 h4
  · rw [du1_NIDXD, toE_zero, add_zero, toE_min, toE_of_ge h0]
    simp
  · rw [du1_PIDXD, toE_of_ge (le_refl INF)]
    simp
  · rw [du1_PIDXD, toE_of_ge (le_refl INF)]
    simp
  · rw [du1_of_ge (by omega) (by omega), min_eq_left h2,
      show DELD + (v1 - v0) - DELD = v1 - v0 from by omega]
    have h := toE_le_add (a := v0) (b := v1 - v0) (by intro _ _; omega)
    rwa [show v0 + (v1 - v0) = v1 from by omega] at h
  · rw [du1_NIDXD, toE_zero, add_zero, min_eq_right (by omega : v1 ≤ v0)]
  · rw [du1_of_lt (by omega : DELD - (v0 - v1) < DELD), toE_zero, add_zero,
      min_eq_right (by omega : v1 ≤ v0)]

/-- The carry-`0` half of the transition rule of equation (29) of
`masked_digit_bound.tex`. -/
theorem toE_dv0_le (Ap Am : Array ℕ) (u0 u1 r : ℕ) :
    toE (dv0 Ap u0 u1 r) ≤ toE (dcost Ap Am u0 u1 r) + toE (du0 (dnext Ap Am u0 u1 r)) := by
  rw [dcost_eq, dnext_eq]
  exact toE_le_cost_add_du0 _ _

/-- The carry-`1` half of the transition rule of equation (29) of
`masked_digit_bound.tex`. -/
theorem toE_dv1_le (Ap Am : Array ℕ) (u0 u1 r : ℕ) :
    toE (dv1 Am u0 u1 r) ≤ toE (dcost Ap Am u0 u1 r) + toE (du1 (dnext Ap Am u0 u1 r)) := by
  rw [dcost_eq, dnext_eq]
  exact toE_le_cost_add_du1 _ _

/-! ## The certificate -/

/-- The carry-`0` soundness condition of the kernel's difference automaton, stated for
arbitrary cost tables so that the two large tables of the kernel are never unfolded. -/
theorem diffCert_sound0_gen (Ap Am : Array ℕ) (a b : ℕ∞) (u0 u1 r : ℕ)
    (ha : a ≤ toE (Ap.getD r INF)) (hb : b ≤ toE (Ap.getD (r + 1) INF)) :
    min (toE u0 + a) (toE u1 + b)
      ≤ toE (dcost Ap Am u0 u1 r) + toE (du0 (dnext Ap Am u0 u1 r)) := by
  refine le_trans ?_ (toE_dv0_le Ap Am u0 u1 r)
  rw [dv0, toE_min]
  exact min_le_min (le_trans (add_le_add (le_refl _) ha) (toE_add_le _ _))
    (le_trans (add_le_add (le_refl _) hb) (toE_add_le _ _))

/-- The carry-`1` soundness condition of the kernel's difference automaton, stated for
arbitrary cost tables. -/
theorem diffCert_sound1_gen (Ap Am : Array ℕ) (a b : ℕ∞) (u0 u1 r : ℕ)
    (ha : a ≤ toE (Am.getD r INF)) (hb : b ≤ toE (Am.getD (r + 1) INF)) :
    min (toE u0 + a) (toE u1 + b)
      ≤ toE (dcost Ap Am u0 u1 r) + toE (du1 (dnext Ap Am u0 u1 r)) := by
  refine le_trans ?_ (toE_dv1_le Ap Am u0 u1 r)
  rw [dv1, toE_min]
  exact min_le_min (le_trans (add_le_add (le_refl _) ha) (toE_add_le _ _))
    (le_trans (add_le_add (le_refl _) hb) (toE_add_le _ _))

theorem wcost_le_ApA_succ (r : ℕ) :
    finalMaskData.wcost ((r : ℤ) + 1) ≤ toE (ApA.getD (r + 1) INF) := by
  rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) from by push_cast; ring]
  exact wcost_le_ApA (r + 1)

theorem wcost_le_AmA_succ (r : ℕ) :
    finalMaskData.wcost ((r : ℤ) + 1 - (finalMaskData.q : ℤ))
      ≤ toE (AmA.getD (r + 1) INF) := by
  rw [show ((r : ℤ) + 1 - (finalMaskData.q : ℤ))
      = ((r + 1 : ℕ) : ℤ) - (finalMaskData.q : ℤ) from by push_cast; ring]
  exact wcost_le_AmA (r + 1)

/-- The carry-`0` soundness condition of the kernel's difference automaton: the relaxed
first line of the transition rule (29) of `masked_digit_bound.tex`. -/
theorem diffCert_sound0 (u0 u1 r : ℕ) :
    min (toE u0 + finalMaskData.wcost (r : ℤ)) (toE u1 + finalMaskData.wcost ((r : ℤ) + 1))
      ≤ toE (dcost ApA AmA u0 u1 r) + toE (du0 (dnext ApA AmA u0 u1 r)) :=
  diffCert_sound0_gen ApA AmA _ _ u0 u1 r (wcost_le_ApA r) (wcost_le_ApA_succ r)

/-- The carry-`1` soundness condition of the kernel's difference automaton: the relaxed
second line of the transition rule (29) of `masked_digit_bound.tex`. -/
theorem diffCert_sound1 (u0 u1 r : ℕ) :
    min (toE u0 + finalMaskData.wcost ((r : ℤ) - (finalMaskData.q : ℤ)))
        (toE u1 + finalMaskData.wcost ((r : ℤ) + 1 - (finalMaskData.q : ℤ)))
      ≤ toE (dcost ApA AmA u0 u1 r) + toE (du1 (dnext ApA AmA u0 u1 r)) :=
  diffCert_sound1_gen ApA AmA _ _ u0 u1 r (wcost_le_AmA r) (wcost_le_AmA_succ r)

/-- The two normalized costs of a state of the kernel's difference automaton are normalized:
the smaller one is `0`. -/
theorem diffCert_norm (s : ℕ) (hs : s < NSD) : toE (du0 s) = 0 ∨ toE (du1 s) = 0 := by
  rcases Nat.lt_or_ge s DELD with h | h
  · right; rw [du1_of_lt h, toE_zero]
  · rcases Nat.lt_or_ge s (2 * DELD + 1) with h2 | h2
    · left; rw [du0_of_ge h (by omega), toE_zero]
    · have hNI : NIDXD = 64001 := rfl
      have hPI : PIDXD = 64002 := rfl
      have hN : NSD = 64003 := rfl
      have hD : DELD = 32000 := rfl
      have hcase : s = NIDXD ∨ s = PIDXD := by omega
      rcases hcase with h' | h'
      · right; rw [h', du1_NIDXD, toE_zero]
      · left; rw [h', du0_PIDXD, toE_zero]

/-- **The difference-side finite carry certificate** of Section 4.3 of
`masked_digit_bound.tex`, as computed by the kernel: the truncated carry graph with
`|δ| ≤ 32000` together with the two extreme states. -/
noncomputable def diffCert : finalMaskData.DiffCert where
  n := NSD
  u0 := fun s => toE (du0 (s : ℕ))
  u1 := fun s => toE (du1 (s : ℕ))
  next := fun s r => ⟨dnext ApA AmA (du0 (s : ℕ)) (du1 (s : ℕ)) r, dnext_lt _ _ _ _ _⟩
  cost := fun s r => toE (dcost ApA AmA (du0 (s : ℕ)) (du1 (s : ℕ)) r)
  start := ⟨PIDXD, by norm_num [NSD, PIDXD]⟩
  u1_start := by
    show toE (du1 PIDXD) = ⊤
    rw [du1_PIDXD, toE_of_ge (le_refl INF)]
  sound0 := fun s r _ => diffCert_sound0 (du0 (s : ℕ)) (du1 (s : ℕ)) r
  sound1 := fun s r _ => diffCert_sound1 (du0 (s : ℕ)) (du1 (s : ℕ)) r
  norm := fun s => diffCert_norm (s : ℕ) s.isLt

/-! ## The row sums -/

/-- A finite cost of the difference automaton is small enough to be looked up in the weight
table. -/
theorem dcost_le {u0 u1 r : ℕ} (h0 : u0 ≤ DELD ∨ u0 = INF) (h1 : u1 ≤ DELD ∨ u1 = INF)
    (h : dcost ApA AmA u0 u1 r < INF) : dcost ApA AmA u0 u1 r ≤ WSZ := by
  have key : ∀ (A : Array ℕ), (∀ i : ℕ, A.getD i INF < INF → A.getD i INF ≤ 2 * CertKernel.B) →
      min (u0 + A.getD r INF) (u1 + A.getD (r + 1) INF) < INF →
      min (u0 + A.getD r INF) (u1 + A.getD (r + 1) INF) ≤ 2 * CertKernel.B + DELD := by
    intro A hA hlt
    rcases min_cases (u0 + A.getD r INF) (u1 + A.getD (r + 1) INF) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at hlt ⊢
      have h2 : A.getD r INF < INF := by
        simp only [INF] at *; omega
      have := hA r h2
      rcases h0 with h0 | h0
      · omega
      · simp only [INF] at *; omega
    · rw [he] at hlt ⊢
      have h2 : A.getD (r + 1) INF < INF := by
        simp only [INF] at *; omega
      have := hA (r + 1) h2
      rcases h1 with h1 | h1
      · omega
      · simp only [INF] at *; omega
  rw [dcost_eq] at h ⊢
  have hb : min (dv0 ApA u0 u1 r) (dv1 AmA u0 u1 r) ≤ 2 * CertKernel.B + DELD := by
    rcases min_cases (dv0 ApA u0 u1 r) (dv1 AmA u0 u1 r) with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he] at h ⊢
      exact key ApA (fun i hi => ApA_le hi) h
    · rw [he] at h ⊢
      exact key AmA (fun i hi => AmA_le hi) h
  simp only [CertKernel.B, DELD, WSZ] at *
  omega

/-- **Each term of a difference-side row sum is a lower bound for the corresponding term of
the Collatz--Wielandt sum**, in units of `2 ^ EE`. -/
theorem dterm_le_real {u0 u1 r : ℕ} (h0 : u0 ≤ DELD ∨ u0 = INF) (h1 : u1 ≤ DELD ∨ u1 = INF) :
    ((dterm ApA AmA m32L e32L diffV u0 u1 r : ℕ) : ℝ)
      ≤ 2 ^ EE * (epow xR (toE (dcost ApA AmA u0 u1 r)) *
          ((diffV.getD (dnext ApA AmA u0 u1 r) 0 : ℕ) : ℝ)) := by
  rw [dterm_eq, epow_toE]
  set a := dcost ApA AmA u0 u1 r with ha
  set ns := dnext ApA AmA u0 u1 r with hns
  split_ifs with h
  · simp
  · have haW : a ≤ WSZ := dcost_le h0 h1 (by omega)
    have hEE : EE ≤ e32L.getD a 0 := EE_le_e32L haW
    have hm := m32L_le haW
    set e := e32L.getD a 0 with he
    set m := m32L.getD a 0 with hm'
    set V := (diffV.getD ns 0 : ℕ) with hV
    refine le_trans (cast_shiftRight_le (m * V) (e - EE)) ?_
    have hVnn : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg _
    have hcast : (((m * V : ℕ)) : ℝ) = (m : ℝ) * (V : ℝ) := by push_cast; ring
    rw [hcast, div_le_iff₀ (by positivity)]
    have hsplit : (2 : ℝ) ^ e = 2 ^ (e - EE) * 2 ^ EE := by
      rw [← pow_add]
      congr 1
      omega
    calc (m : ℝ) * (V : ℝ) ≤ (xR ^ a * 2 ^ e) * (V : ℝ) := by
          exact mul_le_mul_of_nonneg_right hm hVnn
      _ = 2 ^ EE * (xR ^ a * (V : ℝ)) * 2 ^ (e - EE) := by rw [hsplit]; ring

theorem drowAux_eq (Ap Am m32 e32 V : Array ℕ) (u0 u1 : ℕ) :
    ∀ (m : ℕ) (acc : ℕ), drowAux Ap Am m32 e32 V u0 u1 m acc =
      acc + ∑ r ∈ Finset.range m, dterm Ap Am m32 e32 V u0 u1 r := by
  intro m
  induction m with
  | zero => intro acc; simp [drowAux]
  | succ k ih =>
      intro acc
      rw [drowAux, ih, Finset.sum_range_succ]
      omega

theorem drow_eq (s : ℕ) :
    drow ApA AmA m32L e32L diffV s =
      ∑ r ∈ Finset.range CertKernel.Q, dterm ApA AmA m32L e32L diffV (du0 s) (du1 s) r := by
  rw [drow, drowAux_eq]
  omega

/-! ## The Collatz--Wielandt inequality -/

/-- The certificate vector, as a positive real vector on the states. -/
noncomputable def diffVR : Fin diffCert.n → ℝ := fun s => ((diffV.getD (s : ℕ) 0 : ℕ) : ℝ)

theorem diffVR_pos (s : Fin diffCert.n) : 0 < diffVR s := by
  have h := allB_spec diffVPos_true (s : ℕ) s.isLt
  simp only [decide_eq_true_eq] at h
  rw [diffVR]
  exact_mod_cast h

theorem diffCert_cw (s : Fin diffCert.n) :
    (cCert : ℝ) * diffVR s ≤
      ∑ r : Fin finalMaskData.q, epow xR (diffCert.cost s r) * diffVR (diffCert.next s r) := by
  have hq : finalMaskData.q = CertKernel.Q := finalMaskData_q.trans certQ_eq.symm
  have h0 := du0_bound (s : ℕ)
  have h1 := du1_bound (s : ℕ)
  -- the row sum bounds the Collatz--Wielandt sum from below
  have hsum : ((drow ApA AmA m32L e32L diffV (s : ℕ) : ℕ) : ℝ)
      ≤ 2 ^ EE * ∑ r : Fin finalMaskData.q,
          epow xR (diffCert.cost s r) * diffVR (diffCert.next s r) := by
    rw [drow_eq]
    rw [Fin.sum_univ_eq_sum_range
      (fun r => epow xR (diffCert.cost s r) * diffVR (diffCert.next s r)) finalMaskData.q, hq,
      Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    exact dterm_le_real h0 h1
  -- the evaluated test
  have htest := allB_spec diffCheck_true (s : ℕ) s.isLt
  rw [dtest, decide_eq_true_eq, Nat.shiftLeft_eq] at htest
  have htestR : (cNum : ℝ) * ((diffV.getD (s : ℕ) 0 : ℕ) : ℝ) * 2 ^ EE
      ≤ (cDen : ℝ) * ((drow ApA AmA m32L e32L diffV (s : ℕ) : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).2 htest
    push_cast at this
    linarith
  have hEEpos : (0 : ℝ) < 2 ^ EE := by positivity
  have hcNum : ((cNum : ℕ) : ℝ) = 582117820 := by norm_num [cNum]
  have hcDen : ((cDen : ℕ) : ℝ) = 1000000 := by norm_num [cDen]
  have hcCert : (cCert : ℝ) = 582117820 / 1000000 := by
    rw [cCert]; norm_num
  set S := ∑ r : Fin finalMaskData.q,
    epow xR (diffCert.cost s r) * diffVR (diffCert.next s r) with hS
  rw [hcCert, hcNum, hcDen] at *
  have hchain : (582117820 : ℝ) * diffVR s * 2 ^ EE ≤ 1000000 * (2 ^ EE * S) := by
    calc (582117820 : ℝ) * diffVR s * 2 ^ EE
        ≤ 1000000 * ((drow ApA AmA m32L e32L diffV (s : ℕ) : ℕ) : ℝ) := htestR
      _ ≤ 1000000 * (2 ^ EE * S) := by linarith
  have hkey : (582117820 : ℝ) * diffVR s * 2 ^ EE ≤ (1000000 * S) * 2 ^ EE := by linarith
  have := le_of_mul_le_mul_right hkey hEEpos
  linarith

/-- **The difference-side certificate of Section 4.3 of `masked_digit_bound.tex`:**
`log 582.117820 ≤ 𝒫₋(x)`. -/
theorem log_cCert_le_PminusPressure :
    Real.log (cCert : ℝ) ≤ finalMaskData.PminusPressure xR :=
  diffCert.log_le_PminusPressure xR_pos xR_lt_one diffVR (cCert : ℝ) (by norm_num [cCert])
    diffVR_pos diffCert_cw

end MaskedDigit
