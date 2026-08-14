import RequestProject.MaskedCarryFree
import RequestProject.OrientedBlocks

/-!
# Controlled difference blocks

This file formalizes the difference side of Section 4 ("Controlled carries") of
`masked_digit_bound.tex`:

* the block minimum cost `c_k(r)` of equation (16) (`eq:controlled-cost`) and the block
  partition sum `Z_k(x)` of equation (17) (`eq:controlled-Z`);
* Proposition 3 (`prop:controlled-block`), the controlled-carry block bound, equation (18)
  (`eq:controlled-block-bound`);
* Lemma 4 (`lem:controlled-pressure`), the existence of the infinite-block pressure
  `𝒫(x) = lim k⁻¹ log Z_k(x) = sup k⁻¹ log Z_k(x)` and the resulting bound (21)
  (`eq:controlled-limit-bound`).

Throughout, the base is an arbitrary integer `q > B`, so that carries may occur.
-/

open scoped BigOperators
open Filter Topology

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-! ## Signed digit blocks -/

/-- A signed difference word of length `k`: a `k`-tuple of digits from `D = M - M`.  This is
the object over which the minimum in equation (16) of `masked_digit_bound.tex` is taken. -/
abbrev DiffWord (k : ℕ) := Fin k → {d : ℤ // d ∈ D.diffSupport}

/-- Signed difference words are never absent: the all-zero word exists, since `0 ∈ M - M`. -/
instance instNonemptyDiffWord (k : ℕ) : Nonempty (D.DiffWord k) :=
  ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩⟩

/-- The integer value `∑ᵢ dᵢ qⁱ` of a signed difference word. -/
def dwValue {k : ℕ} (v : D.DiffWord k) : ℤ := ∑ i, (v i : ℤ) * (D.q : ℤ) ^ (i : ℕ)

/-- The total minimum witness cost `∑ᵢ κ(dᵢ)` of a signed difference word. -/
noncomputable def dwCost {k : ℕ} (v : D.DiffWord k) : ℕ := ∑ i, D.kappa (v i)

/-- The negation of a signed difference word, used for the evenness `c_k(-r) = c_k(r)` in the
proof of Proposition 3 of `masked_digit_bound.tex`. -/
def dwNeg {k : ℕ} (v : D.DiffWord k) : D.DiffWord k :=
  fun i => ⟨-(v i : ℤ), D.neg_mem_diffSupport (v i).2⟩

/-- The value of a signed difference word is bounded by `q ^ k - 1` in absolute value; this
is the estimate `|∑_{i<k} dᵢ qⁱ| ≤ B (q^k - 1)/(q - 1) ≤ q^k - 1` of Section 4 of
`masked_digit_bound.tex`. -/
theorem abs_dwValue_lt {k : ℕ} (v : D.DiffWord k) : |D.dwValue v| < (D.q : ℤ) ^ k := by
  have hq0 : (0 : ℤ) < (D.q : ℤ) := by
    have := D.q_gt_B; have := D.B_pos
    exact_mod_cast (by omega : 0 < D.q)
  have key : ∀ (m : ℕ) (d : Fin m → ℤ), (∀ i, |d i| ≤ (D.q : ℤ) - 1) →
      |∑ i, d i * (D.q : ℤ) ^ (i : ℕ)| ≤ (D.q : ℤ) ^ m - 1 := by
    intro m
    induction m with
    | zero => intro d _; simp
    | succ n ih =>
      intro d hd
      rw [Fin.sum_univ_castSucc]
      have h1 := ih (fun i => d i.castSucc) (fun i => hd _)
      have hpow : (0 : ℤ) ≤ (D.q : ℤ) ^ n := by positivity
      have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
      have h2 : |d (Fin.last n) * (D.q : ℤ) ^ (Fin.last n : ℕ)| ≤ ((D.q : ℤ) - 1) * (D.q : ℤ) ^ n := by
        rw [abs_mul, hlast, abs_of_nonneg hpow]
        exact mul_le_mul_of_nonneg_right (hd _) hpow
      have h3 := abs_add_le (∑ i : Fin n, d i.castSucc * (D.q : ℤ) ^ ((i.castSucc : ℕ)))
        (d (Fin.last n) * (D.q : ℤ) ^ ((Fin.last n : ℕ)))
      have h4 : ((D.q : ℤ) ^ n - 1) + ((D.q : ℤ) - 1) * (D.q : ℤ) ^ n = (D.q : ℤ) ^ (n + 1) - 1 := by
        ring
      simp only [Fin.val_castSucc] at h3 h1 ⊢
      linarith
  have hd : ∀ i, |(v i : ℤ)| ≤ (D.q : ℤ) - 1 := by
    intro i
    have h1 := D.abs_le_of_mem_diffSupport (v i).2
    have h2 : (D.B : ℤ) ≤ (D.q : ℤ) - 1 := by
      have : (D.B : ℤ) < (D.q : ℤ) := by exact_mod_cast D.q_gt_B
      omega
    linarith
  have hkey := key k (fun i => (v i : ℤ)) hd
  simp only [dwValue]
  linarith

/-! ## The block cost function and partition sum -/

/-- The controlled-carry block cost `c_k(r)` of equation (16) (`eq:controlled-cost`) of
`masked_digit_bound.tex`: the least total witness cost of a signed difference word of length
`k` whose value is congruent to `r` modulo `q ^ k`.  Residues with no such word are exactly
those excluded from `attainableRes`; for them this definition returns `0`, and they are never
used (the source assigns them the value `+∞`). -/
noncomputable def cMinus (k : ℕ) (r : ℤ) : ℕ :=
  sInf {c : ℕ | ∃ v : D.DiffWord k, D.dwValue v ≡ r [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = c}

/-- The set of attainable residues modulo `q ^ k`, denoted `𝒜_k` in the proof of
Proposition 3 of `masked_digit_bound.tex`, represented by their least nonnegative
representatives. -/
noncomputable def attainableRes (k : ℕ) : Finset ℕ :=
  (Finset.range (D.q ^ k)).filter
    fun n => ∃ v : D.DiffWord k, D.dwValue v ≡ (n : ℤ) [ZMOD (D.q : ℤ) ^ k]

/-- The controlled-carry block partition sum `Z_k(x) = ∑_r x^{c_k(r)}` of equation (17)
(`eq:controlled-Z`) of `masked_digit_bound.tex`, with the convention `x^{+∞} = 0` realised by
summing only over the attainable residues. -/
noncomputable def Zminus (x : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ D.attainableRes k, x ^ D.cMinus k (n : ℤ)

/-- A minimum-cost representative exists for every attainable residue. -/
theorem exists_dwCost_eq_cMinus {k : ℕ} {n : ℕ} (hn : n ∈ D.attainableRes k) :
    ∃ v : D.DiffWord k, D.dwValue v ≡ (n : ℤ) [ZMOD (D.q : ℤ) ^ k] ∧
      D.dwCost v = D.cMinus k (n : ℤ) := by
  have hne : {c : ℕ | ∃ v : D.DiffWord k,
      D.dwValue v ≡ (n : ℤ) [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = c}.Nonempty := by
    simp only [attainableRes, Finset.mem_filter] at hn
    obtain ⟨v, hv⟩ := hn.2
    exact ⟨D.dwCost v, v, hv, rfl⟩
  obtain ⟨v, hv, hc⟩ := Nat.sInf_mem hne
  exact ⟨v, hv, hc⟩

/-- `c_k` never exceeds the cost of any representing word. -/
theorem cMinus_le {k : ℕ} {r : ℤ} (v : D.DiffWord k) (hv : D.dwValue v ≡ r [ZMOD (D.q : ℤ) ^ k]) :
    D.cMinus k r ≤ D.dwCost v :=
  Nat.sInf_le ⟨v, hv, rfl⟩

/-- Negating all difference digits negates the value of a word (proof of Proposition 3 of
`masked_digit_bound.tex`). -/
theorem dwValue_dwNeg {k : ℕ} (v : D.DiffWord k) : D.dwValue (D.dwNeg v) = - D.dwValue v := by
  simp [dwValue, dwNeg]

/-- Negating all difference digits preserves the cost, since `κ` is even (proof of
Proposition 3 of `masked_digit_bound.tex`). -/
theorem dwCost_dwNeg {k : ℕ} (v : D.DiffWord k) : D.dwCost (D.dwNeg v) = D.dwCost v := by
  simp [dwCost, dwNeg, D.kappa_neg]

/-- **Evenness of the block cost**: `c_k(-r) = c_k(r)`, proved in the source by negating all
difference digits (proof of Proposition 3 of `masked_digit_bound.tex`). -/
theorem cMinus_neg (k : ℕ) (r : ℤ) : D.cMinus k (-r) = D.cMinus k r := by
  have hset : {c : ℕ | ∃ v : D.DiffWord k,
        D.dwValue v ≡ (-r) [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = c}
      = {c : ℕ | ∃ v : D.DiffWord k,
        D.dwValue v ≡ r [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = c} := by
    ext c
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨D.dwNeg v, by rw [D.dwValue_dwNeg v]; simpa using hv.neg, D.dwCost_dwNeg v⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨D.dwNeg v, by rw [D.dwValue_dwNeg v]; exact hv.neg, D.dwCost_dwNeg v⟩
  rw [cMinus, cMinus, hset]

/-- The zero residue is always attainable, by the all-zero difference word. -/
theorem zero_mem_attainableRes (k : ℕ) : (0 : ℕ) ∈ D.attainableRes k := by
  have hq0 : 0 < D.q ^ k := pow_pos (by have := D.q_gt_B; have := D.B_pos; omega) k
  simp only [attainableRes, Finset.mem_filter, Finset.mem_range]
  exact ⟨hq0, ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩, by simp [dwValue]⟩⟩

/-- `Z_k(x) > 0` for `x > 0`: the zero residue is always attainable. -/
theorem Zminus_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < D.Zminus x k :=
  Finset.sum_pos (fun _ _ => pow_pos hx _) ⟨0, D.zero_mem_attainableRes k⟩

/-- `Z_k(x) ≤ q ^ k`, since there are at most `q ^ k` residues and `x ≤ 1`. -/
theorem Zminus_le_pow {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    D.Zminus x k ≤ (D.q : ℝ) ^ k := by
  have hcard : (D.attainableRes k).card ≤ D.q ^ k := by
    have h := Finset.card_filter_le (Finset.range (D.q ^ k))
      (fun n => ∃ v : D.DiffWord k, D.dwValue v ≡ (n : ℤ) [ZMOD (D.q : ℤ) ^ k])
    simpa [attainableRes] using h
  calc D.Zminus x k ≤ ∑ _n ∈ D.attainableRes k, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => pow_le_one₀ hx0.le hx1
    _ = ((D.attainableRes k).card : ℝ) := by simp
    _ ≤ ((D.q ^ k : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (D.q : ℝ) ^ k := by push_cast; ring

/-- `Z₀(x) = 1`. -/
theorem Zminus_zero {x : ℝ} : D.Zminus x 0 = 1 := by
  have hA : D.attainableRes 0 = {0} := by
    ext n
    simp only [attainableRes, Finset.mem_filter, Finset.mem_range, pow_zero,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩; omega
    · rintro rfl
      exact ⟨by norm_num, ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩, Int.modEq_one⟩⟩
  have hc : D.cMinus 0 (0 : ℤ) = 0 :=
    Nat.le_zero.1 (Nat.sInf_le ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩, Int.modEq_one, by
      simp [dwCost]⟩)
  simp [Zminus, hA, hc]

/-- Concatenation of two signed difference words, the operation used in the proof of Lemma 4
(`lem:controlled-pressure`) of `masked_digit_bound.tex` to concatenate minimum-cost
representatives of two blocks. -/
def dwAppend {k l : ℕ} (u : D.DiffWord k) (w : D.DiffWord l) : D.DiffWord (k + l) :=
  Fin.append u w

/-- The value of a concatenation, `val(u ⧺ w) = val(u) + q^k val(w)` (proof of Lemma 4 of
`masked_digit_bound.tex`). -/
theorem dwValue_append {k l : ℕ} (u : D.DiffWord k) (w : D.DiffWord l) :
    D.dwValue (D.dwAppend u w) = D.dwValue u + (D.q : ℤ) ^ k * D.dwValue w := by
  simp only [dwValue, dwAppend]
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      simp [Fin.append_left]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.natAdd k i : Fin (k + l)) : ℕ) = k + (i : ℕ) := rfl
    simp only [Fin.append_right, hi, pow_add]
    ring

/-- The cost of a concatenation is the sum of the costs (proof of Lemma 4 of
`masked_digit_bound.tex`). -/
theorem dwCost_append {k l : ℕ} (u : D.DiffWord k) (w : D.DiffWord l) :
    D.dwCost (D.dwAppend u w) = D.dwCost u + D.dwCost w := by
  simp only [dwCost, dwAppend]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- **Supermultiplicativity of the block partition sum**, the inequality
`Z_{k+ℓ}(x) ≥ Z_k(x) Z_ℓ(x)` established in the proof of Lemma 4
(`lem:controlled-pressure`) of `masked_digit_bound.tex` by concatenating minimum-cost
representatives. -/
theorem Zminus_supermultiplicative {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k l : ℕ) :
    D.Zminus x k * D.Zminus x l ≤ D.Zminus x (k + l) := by
  classical
  have hq0 : (0 : ℤ) < (D.q : ℤ) := by
    have := D.q_gt_B; have := D.B_pos
    exact_mod_cast (by omega : 0 < D.q)
  have hqkl : (0 : ℤ) < (D.q : ℤ) ^ (k + l) := pow_pos hq0 _
  have hnat_eq : ∀ (m a b : ℕ), a < D.q ^ m → b < D.q ^ m →
      (a : ℤ) ≡ (b : ℤ) [ZMOD (D.q : ℤ) ^ m] → a = b := by
    intro m a b ha hb h
    have hqm : ((D.q : ℤ)) ^ m = ((D.q ^ m : ℕ) : ℤ) := by push_cast; ring
    rw [Int.ModEq, hqm, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb)] at h
    exact_mod_cast h
  have hex : ∀ (m : ℕ) (n : ℕ), ∃ v : D.DiffWord m, n ∈ D.attainableRes m →
      (D.dwValue v ≡ (n : ℤ) [ZMOD (D.q : ℤ) ^ m] ∧ D.dwCost v = D.cMinus m (n : ℤ)) := by
    intro m n
    by_cases h : n ∈ D.attainableRes m
    · obtain ⟨v, hv⟩ := D.exists_dwCost_eq_cMinus h
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩, fun h' => absurd h' h⟩
  choose rep hrep using hex
  set F : Finset (ℕ × ℕ) := (D.attainableRes k) ×ˢ (D.attainableRes l) with hFdef
  set T : ℕ × ℕ → ℕ := fun p =>
    (D.dwValue (D.dwAppend (rep k p.1) (rep l p.2)) % (D.q : ℤ) ^ (k + l)).toNat with hTdef
  have hTcast : ∀ p : ℕ × ℕ, ((T p : ℕ) : ℤ)
      = D.dwValue (D.dwAppend (rep k p.1) (rep l p.2)) % (D.q : ℤ) ^ (k + l) := by
    intro p
    simp only [hTdef]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (ne_of_gt hqkl))
  have hTlt : ∀ p : ℕ × ℕ, T p < D.q ^ (k + l) := by
    intro p
    have h := Int.emod_lt_of_pos (D.dwValue (D.dwAppend (rep k p.1) (rep l p.2))) hqkl
    have h2 : ((T p : ℕ) : ℤ) < ((D.q ^ (k + l) : ℕ) : ℤ) := by
      rw [hTcast p]; push_cast; exact h
    exact_mod_cast h2
  have hTmod : ∀ p : ℕ × ℕ,
      ((T p : ℕ) : ℤ) ≡ D.dwValue (D.dwAppend (rep k p.1) (rep l p.2)) [ZMOD (D.q : ℤ) ^ (k + l)] := by
    intro p
    rw [Int.ModEq, hTcast p]
    exact Int.emod_emod_of_dvd _ dvd_rfl
  have hTmem : ∀ p ∈ F, T p ∈ D.attainableRes (k + l) := by
    intro p _
    simp only [attainableRes, Finset.mem_filter, Finset.mem_range]
    exact ⟨hTlt p, ⟨D.dwAppend (rep k p.1) (rep l p.2), (hTmod p).symm⟩⟩
  have hTcost : ∀ p ∈ F, D.cMinus (k + l) ((T p : ℕ) : ℤ)
      ≤ D.cMinus k (p.1 : ℤ) + D.cMinus l (p.2 : ℤ) := by
    intro p hp
    rw [hFdef, Finset.mem_product] at hp
    have h1 := hrep k p.1 hp.1
    have h2 := hrep l p.2 hp.2
    have hle := D.cMinus_le (D.dwAppend (rep k p.1) (rep l p.2)) (hTmod p).symm
    rw [D.dwCost_append, h1.2, h2.2] at hle
    exact hle
  have hinj : Set.InjOn T (F : Set (ℕ × ℕ)) := by
    intro p hp p' hp' hpp
    simp only [Finset.mem_coe, hFdef, Finset.mem_product] at hp hp'
    have hp1 := (hrep k p.1 hp.1).1
    have hp2 := (hrep l p.2 hp.2).1
    have hp1' := (hrep k p'.1 hp'.1).1
    have hp2' := (hrep l p'.2 hp'.2).1
    have hVal : D.dwValue (D.dwAppend (rep k p.1) (rep l p.2))
        ≡ D.dwValue (D.dwAppend (rep k p'.1) (rep l p'.2)) [ZMOD (D.q : ℤ) ^ (k + l)] :=
      ((hTmod p).symm.trans (by rw [hpp])).trans (hTmod p')
    have hltgen : ∀ (m n : ℕ), n ∈ D.attainableRes m → n < D.q ^ m := by
      intro m n h
      simp only [attainableRes, Finset.mem_filter, Finset.mem_range] at h
      exact h.1
    have hlt1 : p.1 < D.q ^ k := hltgen k p.1 hp.1
    have hlt1' : p'.1 < D.q ^ k := hltgen k p'.1 hp'.1
    have hlt2 : p.2 < D.q ^ l := hltgen l p.2 hp.2
    have hlt2' : p'.2 < D.q ^ l := hltgen l p'.2 hp'.2
    -- first coordinate
    have hdvdk : ((D.q : ℤ)) ^ k ∣ ((D.q : ℤ)) ^ (k + l) := pow_dvd_pow _ (Nat.le_add_right k l)
    have hValk : D.dwValue (D.dwAppend (rep k p.1) (rep l p.2))
        ≡ D.dwValue (D.dwAppend (rep k p'.1) (rep l p'.2)) [ZMOD (D.q : ℤ) ^ k] :=
      hVal.of_dvd hdvdk
    have hred : ∀ (a : ℕ) (w : D.DiffWord l),
        D.dwValue (D.dwAppend (rep k a) w) ≡ D.dwValue (rep k a) [ZMOD (D.q : ℤ) ^ k] := by
      intro a w
      rw [D.dwValue_append]
      exact Int.modEq_iff_dvd.2 ⟨-D.dwValue w, by ring⟩
    have h1eq : p.1 = p'.1 := by
      refine hnat_eq k p.1 p'.1 hlt1 hlt1' ?_
      exact (hp1.symm.trans ((hred p.1 (rep l p.2)).symm.trans
        (hValk.trans ((hred p'.1 (rep l p'.2)).trans hp1'))))
    -- second coordinate
    have h2eq : p.2 = p'.2 := by
      refine hnat_eq l p.2 p'.2 hlt2 hlt2' ?_
      have hVal' : (D.q : ℤ) ^ (k + l) ∣
          ((D.q : ℤ) ^ k * D.dwValue (rep l p.2) - (D.q : ℤ) ^ k * D.dwValue (rep l p'.2)) := by
        have := Int.ModEq.dvd hVal.symm
        rw [D.dwValue_append, D.dwValue_append, h1eq] at this
        have heq : D.dwValue (rep k p'.1) + (D.q : ℤ) ^ k * D.dwValue (rep l p.2) -
            (D.dwValue (rep k p'.1) + (D.q : ℤ) ^ k * D.dwValue (rep l p'.2))
            = (D.q : ℤ) ^ k * D.dwValue (rep l p.2) - (D.q : ℤ) ^ k * D.dwValue (rep l p'.2) := by
          ring
        rw [heq] at this
        exact this
      have hfac : (D.q : ℤ) ^ k * D.dwValue (rep l p.2) - (D.q : ℤ) ^ k * D.dwValue (rep l p'.2)
          = (D.q : ℤ) ^ k * (D.dwValue (rep l p.2) - D.dwValue (rep l p'.2)) := by ring
      rw [hfac, pow_add] at hVal'
      have hk0 : ((D.q : ℤ) ^ k) ≠ 0 := ne_of_gt (pow_pos hq0 k)
      have hdvd : (D.q : ℤ) ^ l ∣ (D.dwValue (rep l p.2) - D.dwValue (rep l p'.2)) :=
        (mul_dvd_mul_iff_left hk0).mp hVal'
      have hmod : D.dwValue (rep l p.2) ≡ D.dwValue (rep l p'.2) [ZMOD (D.q : ℤ) ^ l] :=
        Int.ModEq.symm (Int.modEq_iff_dvd.2 hdvd)
      exact hp2.symm.trans (hmod.trans hp2')
    exact Prod.ext h1eq h2eq
  have hsub : F.image T ⊆ D.attainableRes (k + l) := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ht
    exact hTmem p hp
  have hprod : D.Zminus x k * D.Zminus x l
      = ∑ p ∈ F, x ^ (D.cMinus k (p.1 : ℤ) + D.cMinus l (p.2 : ℤ)) := by
    rw [hFdef, Finset.sum_product, Zminus, Zminus, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (pow_add x _ _).symm
  calc D.Zminus x k * D.Zminus x l
      = ∑ p ∈ F, x ^ (D.cMinus k (p.1 : ℤ) + D.cMinus l (p.2 : ℤ)) := hprod
    _ ≤ ∑ p ∈ F, x ^ D.cMinus (k + l) ((T p : ℕ) : ℤ) :=
        Finset.sum_le_sum fun p hp => pow_le_pow_of_le_one hx0.le hx1.le (hTcost p hp)
    _ = ∑ t ∈ F.image T, x ^ D.cMinus (k + l) ((t : ℕ) : ℤ) := (Finset.sum_image (f := fun t : ℕ => x ^ D.cMinus (k + l) ((t : ℕ) : ℤ)) hinj).symm
    _ ≤ D.Zminus x (k + l) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hx0.le _

/-- Iterated supermultiplicativity: `Z_k(x)^n ≤ Z_{nk}(x)` (proof of Lemma 4,
`lem:controlled-pressure`, of `masked_digit_bound.tex`). -/
theorem Zminus_pow_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (k n : ℕ) :
    (D.Zminus x k) ^ n ≤ D.Zminus x (n * k) := by
  induction n with
  | zero => simp [D.Zminus_zero]
  | succ n ih =>
      have h1 := D.Zminus_supermultiplicative hx0 hx1 (n * k) k
      have h2 : (D.Zminus x k) ^ n * D.Zminus x k ≤ D.Zminus x (n * k) * D.Zminus x k :=
        mul_le_mul_of_nonneg_right ih (D.Zminus_pos hx0 k).le
      have h3 : (n + 1) * k = n * k + k := by ring
      rw [pow_succ, h3]
      linarith

/-- The residue `B` is attainable in a single block, since `B ∈ D = M - M`
(Section 4 of `masked_digit_bound.tex`). -/
theorem B_mem_attainableRes_one : D.B ∈ D.attainableRes 1 := by
  have hB : D.B < D.q := D.q_gt_B
  simp only [attainableRes, Finset.mem_filter, Finset.mem_range, pow_one]
  refine ⟨hB, ⟨fun _ => ⟨(D.B : ℤ), D.B_mem_diffSupport⟩, ?_⟩⟩
  simp [dwValue]

/-- `c_1(0) = 0`: the all-zero word represents the zero residue at no cost. -/
theorem cMinus_zero_eq_zero (k : ℕ) : D.cMinus k 0 = 0 :=
  Nat.le_zero.1 (Nat.sInf_le ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩, by simp [dwValue], by
    simp [dwCost, D.kappa_zero]⟩)

/-- `Z_1(x) > 1` for `0 < x`: the residues `0` and `B` are both attainable and distinct
(Section 4 of `masked_digit_bound.tex`). -/
theorem one_lt_Zminus_one {x : ℝ} (hx0 : 0 < x) : 1 < D.Zminus x 1 := by
  classical
  have hB0 : 0 < D.B := D.B_pos
  have hsub : ({0, D.B} : Finset ℕ) ⊆ D.attainableRes 1 := by
    intro n hn
    rcases Finset.mem_insert.1 hn with rfl | hn
    · exact D.zero_mem_attainableRes 1
    · rw [Finset.mem_singleton.1 hn]; exact D.B_mem_attainableRes_one
  have hne : (0 : ℕ) ≠ D.B := by omega
  have hsum : ∑ n ∈ ({0, D.B} : Finset ℕ), x ^ D.cMinus 1 (n : ℤ)
      = 1 + x ^ D.cMinus 1 ((D.B : ℕ) : ℤ) := by
    rw [Finset.sum_pair hne]
    simp [D.cMinus_zero_eq_zero]
  have hle : ∑ n ∈ ({0, D.B} : Finset ℕ), x ^ D.cMinus 1 (n : ℤ) ≤ D.Zminus x 1 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hx0.le _
  have hpos : 0 < x ^ D.cMinus 1 ((D.B : ℕ) : ℤ) := pow_pos hx0 _
  rw [hsum] at hle
  linarith

/-- `Z_k(x) > 1` for `k ≥ 1`, hence `Z_k(x)^n → ∞`; used in the passage to the limit in
Lemma 4 (`lem:controlled-pressure`) of `masked_digit_bound.tex`. -/
theorem one_lt_Zminus {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {k : ℕ} (hk : 1 ≤ k) :
    1 < D.Zminus x k := by
  have h := D.Zminus_pow_le hx0 hx1 1 k
  rw [mul_one] at h
  have h2 : 1 < (D.Zminus x 1) ^ k :=
    one_lt_pow₀ (D.one_lt_Zminus_one hx0) (by omega)
  linarith

/-- The block cost `c_k(r)` depends only on the residue of `r` modulo `q^k` (implicit in
the definition (12), `eq:controlled-cost`, of `masked_digit_bound.tex`). -/
theorem cMinus_congr {k : ℕ} {r r' : ℤ} (h : r ≡ r' [ZMOD (D.q : ℤ) ^ k]) :
    D.cMinus k r = D.cMinus k r' := by
  have hset : {c : ℕ | ∃ v : D.DiffWord k, D.dwValue v ≡ r [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = c}
      = {c : ℕ | ∃ v : D.DiffWord k,
          D.dwValue v ≡ r' [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = c} := by
    ext c
    exact ⟨fun ⟨v, hv, hc⟩ => ⟨v, hv.trans h, hc⟩, fun ⟨v, hv, hc⟩ => ⟨v, hv.trans h.symm, hc⟩⟩
  rw [cMinus, cMinus, hset]

/-- The set of attainable residues is stable under `n ↦ q^k - n`, since difference words may
be negated (proof of Proposition 3, `prop:controlled-block`, of `masked_digit_bound.tex`). -/
theorem sub_mem_attainableRes {k n : ℕ} (hn : n ∈ D.attainableRes k) (hn0 : n ≠ 0) :
    D.q ^ k - n ∈ D.attainableRes k := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hlt : n < D.q ^ k := by
    simp only [attainableRes, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1
  obtain ⟨v, hv⟩ := D.exists_dwCost_eq_cMinus hn
  simp only [attainableRes, Finset.mem_filter, Finset.mem_range]
  refine ⟨by omega, ⟨D.dwNeg v, ?_⟩⟩
  have hcast : ((D.q ^ k - n : ℕ) : ℤ) = (D.q : ℤ) ^ k - (n : ℤ) := by
    have : ((D.q ^ k : ℕ) : ℤ) = (D.q : ℤ) ^ k := by push_cast; ring
    rw [Nat.cast_sub hlt.le, this]
  rw [D.dwValue_dwNeg, hcast]
  have h1 : -D.dwValue v ≡ -(n : ℤ) [ZMOD (D.q : ℤ) ^ k] := hv.1.neg
  have h2 : -(n : ℤ) ≡ (D.q : ℤ) ^ k - (n : ℤ) [ZMOD (D.q : ℤ) ^ k] :=
    Int.modEq_iff_dvd.2 ⟨1, by ring⟩
  exact h1.trans h2

/-- `c_k(q^k - n) = c_k(n)`, the evenness of the block cost in the form used in the proof of
Proposition 3 (`prop:controlled-block`) of `masked_digit_bound.tex`. -/
theorem cMinus_sub {k n : ℕ} (hn : n ≤ D.q ^ k) :
    D.cMinus k ((D.q ^ k - n : ℕ) : ℤ) = D.cMinus k (n : ℤ) := by
  have hcast : ((D.q ^ k - n : ℕ) : ℤ) = (D.q : ℤ) ^ k - (n : ℤ) := by
    have : ((D.q ^ k : ℕ) : ℤ) = (D.q : ℤ) ^ k := by push_cast; ring
    rw [Nat.cast_sub hn, this]
  rw [hcast]
  have h2 : (D.q : ℤ) ^ k - (n : ℤ) ≡ -(n : ℤ) [ZMOD (D.q : ℤ) ^ k] :=
    Int.modEq_iff_dvd.2 ⟨-1, by ring⟩
  rw [D.cMinus_congr h2, D.cMinus_neg]

/-- A difference word of zero total cost is the all-zero word, since `κ(d) > 0` for `d ≠ 0`
(proof of Proposition 3, `prop:controlled-block`, of `masked_digit_bound.tex`). -/
theorem eq_zero_of_dwCost_eq_zero {k : ℕ} (v : D.DiffWord k) (h : D.dwCost v = 0) (i : Fin k) :
    ((v i : ℤ)) = 0 := by
  by_contra hne
  have hpos : 0 < D.kappa (v i) := D.kappa_pos (v i).2 hne
  have hzero : ∀ j ∈ (Finset.univ : Finset (Fin k)), D.kappa (v j) = 0 :=
    (Finset.sum_eq_zero_iff).1 h
  exact absurd (hzero i (Finset.mem_univ i)) (by omega)

/-! ## The nonzero self-inverse residue -/

/-- **A nonzero self-inverse residue is represented by `q^k/2`.**  If `0 < n < q^k` satisfies
`n ≡ -n` modulo `q^k`, then `2n = q^k`.  This is the assertion of the proof of Proposition 3
(`prop:controlled-block`) of `masked_digit_bound.tex` that "the zero residue is always
self-inverse; when `q^k` is even, the only other self-inverse residue is `h = q^k/2`". -/
theorem two_mul_eq_of_self_inverse {k n : ℕ} (hlt : n < D.q ^ k) (hn0 : n ≠ 0)
    (hself : (n : ℤ) ≡ -(n : ℤ) [ZMOD (D.q : ℤ) ^ k]) : 2 * n = D.q ^ k := by
  have hqkZ : ((D.q ^ k : ℕ) : ℤ) = (D.q : ℤ) ^ k := by push_cast; ring
  have hdvdZ : (D.q : ℤ) ^ k ∣ 2 * (n : ℤ) := by
    have h := hself.dvd
    have he : -(n : ℤ) - (n : ℤ) = -(2 * (n : ℤ)) := by ring
    rw [he] at h
    exact (dvd_neg.1 h)
  have hdvd : D.q ^ k ∣ 2 * n := by
    have : ((D.q ^ k : ℕ) : ℤ) ∣ ((2 * n : ℕ) : ℤ) := by rw [hqkZ]; push_cast; exact hdvdZ
    exact_mod_cast this
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : c < 2 := by
    by_contra hcon
    push_neg at hcon
    have : D.q ^ k * 2 ≤ D.q ^ k * c := Nat.mul_le_mul_left _ hcon
    omega
  interval_cases c <;> omega

/-- **Uniqueness of the nonzero self-inverse residue.**  Two nonzero self-inverse residues
modulo `q^k`, taken in `[0, q^k)`, are equal — both are `q^k/2` (proof of Proposition 3,
`prop:controlled-block`, of `masked_digit_bound.tex`). -/
theorem self_inverse_res_unique {k m n : ℕ} (hm : m < D.q ^ k) (hm0 : m ≠ 0)
    (hmself : (m : ℤ) ≡ -(m : ℤ) [ZMOD (D.q : ℤ) ^ k]) (hn : n < D.q ^ k) (hn0 : n ≠ 0)
    (hnself : (n : ℤ) ≡ -(n : ℤ) [ZMOD (D.q : ℤ) ^ k]) : m = n := by
  have h1 := D.two_mul_eq_of_self_inverse hm hm0 hmself
  have h2 := D.two_mul_eq_of_self_inverse hn hn0 hnself
  omega

/-- The residue `B` is attainable in every block length `k ≥ 1`, by the word with the single
digit `B` in the lowest position (Section 4 of `masked_digit_bound.tex`). -/
theorem B_mem_attainableRes {k : ℕ} (hk : 0 < k) : D.B ∈ D.attainableRes k := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqle : D.q ≤ D.q ^ k := Nat.le_self_pow (by omega) D.q
  have hlt : D.B < D.q ^ k := lt_of_lt_of_le D.q_gt_B hqle
  simp only [attainableRes, Finset.mem_filter, Finset.mem_range]
  refine ⟨hlt, ⟨fun i => if (i : ℕ) = 0 then ⟨(D.B : ℤ), D.B_mem_diffSupport⟩
    else ⟨0, D.zero_mem_diffSupport⟩, ?_⟩⟩
  have hval : D.dwValue (fun i : Fin k => if (i : ℕ) = 0
      then (⟨(D.B : ℤ), D.B_mem_diffSupport⟩ : {d : ℤ // d ∈ D.diffSupport})
      else ⟨0, D.zero_mem_diffSupport⟩) = (D.B : ℤ) := by
    rw [dwValue, Finset.sum_eq_single (⟨0, hk⟩ : Fin k)]
    · simp
    · intro b _ hb
      have hb0 : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [hb0]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hval]

/-! ## The controlled-carry block bound -/

set_option maxHeartbeats 1000000 in
/-- **Proposition 3 (Controlled-carry block bound)** of `masked_digit_bound.tex`,
equation (18) (`eq:controlled-block-bound`), in the general form in which the sum side is
supplied as an abstract weighted bound `|sumSet m T| x^T ≤ C · Pp^m`.  Taking
`Pp = P₊(x)`, `C = 1` gives equation (18) itself (`controlled_block_bound`); taking
`Pp = W_ℓ(x)^{1/ℓ}` gives the two-block bound (25) (`eq:finite-two-block-bound`) of
Proposition 5.

The alphabet is the *whole* attainable residue set `𝒜_k`, so the bound involves the full
block partition sum `Z_k(x)` of equation (17), exactly as in the source.  The possible
nonzero self-inverse residue `h = q^k/2` is retained: it is its own negative, and it is
handled as in the source, by keeping only the words in which it occurs an even number of
times and orienting its occurrences alternately as `d(h)` and `-d(h)` from left to right
(see `MaskData.core_bound_oriented`). -/
theorem controlled_block_bound_gen (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) (hk : 0 < k)
    (Pp C : ℝ) (hPp0 : 0 < Pp) (hC0 : 0 < C)
    (hPp : ∀ m T : ℕ, ((D.sumSet m T).card : ℝ) * x ^ T ≤ C * Pp ^ m) :
    1 + (Real.log (D.Zminus x k) / k - Real.log Pp) / Real.log D.q ≤ C3a := by
  classical
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqk : 0 < D.q ^ k := pow_pos (by omega) k
  have hqkZ : ((D.q ^ k : ℕ) : ℤ) = (D.q : ℤ) ^ k := by push_cast; ring
  -- minimum-cost representatives of the attainable residues
  have hex : ∀ n : ℕ, ∃ v : D.DiffWord k, n ∈ D.attainableRes k →
      (D.dwValue v ≡ (n : ℤ) [ZMOD (D.q : ℤ) ^ k] ∧ D.dwCost v = D.cMinus k (n : ℤ)) := by
    intro n
    by_cases h : n ∈ D.attainableRes k
    · obtain ⟨v, hv⟩ := D.exists_dwCost_eq_cMinus h
      exact ⟨v, fun _ => hv⟩
    · exact ⟨fun _ => ⟨0, D.zero_mem_diffSupport⟩, fun h' => absurd h' h⟩
  choose rep hrep using hex
  -- the alphabet: *all* attainable residues
  set S : Finset ℕ := D.attainableRes k with hSdef
  have hattlt : ∀ n : ℕ, n ∈ S → n < D.q ^ k := by
    intro n hn
    rw [hSdef] at hn
    simp only [attainableRes, Finset.mem_filter, Finset.mem_range] at hn
    exact hn.1
  have h0S : (0 : ℕ) ∈ S := D.zero_mem_attainableRes k
  have hBS : D.B ∈ S := D.B_mem_attainableRes hk
  have hnegS : ∀ n ∈ S, (if n = 0 then 0 else D.q ^ k - n) ∈ S := by
    intro n hn
    by_cases h0 : n = 0
    · simp [h0, h0S]
    · rw [if_neg h0]
      exact D.sub_mem_attainableRes hn h0
  -- the alphabet type and the digit blocks attached to its letters
  set A : Type := {n : ℕ // n ∈ S} with hAdef
  have hneA : Nonempty A := ⟨⟨0, h0S⟩⟩
  haveI hntA : Nontrivial A := by
    refine ⟨⟨⟨0, h0S⟩, ⟨D.B, hBS⟩, ?_⟩⟩
    intro hcon
    have h := congrArg (fun z : A => (z : ℕ)) hcon
    simp only at h
    have := D.B_pos
    omega
  set vec : A → Fin k → ℤ := fun a i =>
    if 2 * (a : ℕ) ≤ D.q ^ k then ((rep (a : ℕ) i : ℤ))
    else -((rep (D.q ^ k - (a : ℕ)) i : ℤ)) with hvecdef
  have hvec : ∀ (a : A) (i : Fin k), vec a i ∈ D.diffSupport := by
    intro a i
    rw [hvecdef]
    by_cases h : 2 * (a : ℕ) ≤ D.q ^ k
    · simp [h]
    · simpa [h] using D.neg_mem_diffSupport (rep (D.q ^ k - (a : ℕ)) i).2
  -- for a letter `n`, the block represents `n` modulo `q^k` and has cost `c_k(n)`
  have hkey : ∀ a : A, D.blockVal k (vec a) ≡ ((a : ℕ) : ℤ) [ZMOD (D.q : ℤ) ^ k] ∧
      D.blockCost k (vec a) = D.cMinus k (((a : ℕ) : ℤ)) := by
    intro a
    have hatt : (a : ℕ) ∈ S := a.2
    have hlt := hattlt _ hatt
    by_cases h : 2 * (a : ℕ) ≤ D.q ^ k
    · have hrp := hrep (a : ℕ) hatt
      constructor
      · have : D.blockVal k (vec a) = D.dwValue (rep (a : ℕ)) := by
          simp only [blockVal, dwValue, hvecdef, h, if_true]
        rw [this]; exact hrp.1
      · have : D.blockCost k (vec a) = D.dwCost (rep (a : ℕ)) := by
          simp only [blockCost, dwCost, hvecdef, h, if_true]
        rw [this]; exact hrp.2
    · have h0 : (a : ℕ) ≠ 0 := by
        intro h0; rw [h0] at h; simp at h
      have hmatt := D.sub_mem_attainableRes hatt h0
      have hrp := hrep (D.q ^ k - (a : ℕ)) hmatt
      have hcast : ((D.q ^ k - (a : ℕ) : ℕ) : ℤ) = (D.q : ℤ) ^ k - ((a : ℕ) : ℤ) := by
        rw [Nat.cast_sub hlt.le, hqkZ]
      constructor
      · have hb : D.blockVal k (vec a) = -D.dwValue (rep (D.q ^ k - (a : ℕ))) := by
          simp only [blockVal, dwValue, hvecdef, h, if_false, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hb]
        have h1 : -D.dwValue (rep (D.q ^ k - (a : ℕ)))
            ≡ -((D.q ^ k - (a : ℕ) : ℕ) : ℤ) [ZMOD (D.q : ℤ) ^ k] := hrp.1.neg
        refine h1.trans ?_
        rw [hcast]
        exact Int.modEq_iff_dvd.2 ⟨1, by ring⟩
      · have hb : D.blockCost k (vec a) = D.dwCost (rep (D.q ^ k - (a : ℕ))) := by
          simp only [blockCost, dwCost, hvecdef, h, if_false]
          exact Finset.sum_congr rfl fun i _ => D.kappa_neg _
        rw [hb, hrp.2, D.cMinus_sub hlt.le]
  -- the involution
  set neg : A → A := fun a => ⟨if (a : ℕ) = 0 then 0 else D.q ^ k - (a : ℕ), hnegS _ a.2⟩
    with hnegdef
  have hneginv : Function.Involutive neg := by
    intro a
    refine Subtype.ext ?_
    have hlt := hattlt _ a.2
    by_cases h0 : (a : ℕ) = 0
    · simp [hnegdef, h0]
    · have hne0 : D.q ^ k - (a : ℕ) ≠ 0 := by
        have : 0 < (a : ℕ) := Nat.pos_of_ne_zero h0
        omega
      simp only [hnegdef, h0, if_false, hne0]
      omega
  -- the self-inverse letter, if there is one; otherwise the zero letter
  obtain ⟨hh, hhcase, hhspec⟩ : ∃ hh : A, ((hh : ℕ) = 0 ∨ 2 * (hh : ℕ) = D.q ^ k) ∧
      (∀ a : A, (a : ℕ) ≠ 0 → 2 * (a : ℕ) = D.q ^ k → a = hh) := by
    by_cases hexh : ∃ n : A, (n : ℕ) ≠ 0 ∧ 2 * (n : ℕ) = D.q ^ k
    · obtain ⟨n, hn0, hn2⟩ := hexh
      exact ⟨n, Or.inr hn2, fun a ha0 ha2 => Subtype.ext (by omega)⟩
    · push_neg at hexh
      exact ⟨⟨0, h0S⟩, Or.inl rfl, fun a ha0 ha2 => absurd ha2 (hexh a ha0)⟩
  have hhnegh : neg hh = hh := by
    refine Subtype.ext ?_
    rcases hhcase with h0 | h2
    · simp [hnegdef, h0]
    · have hne0 : (hh : ℕ) ≠ 0 := by
        intro hcon; rw [hcon] at h2; omega
      simp only [hnegdef, hne0, if_false]
      omega
  -- away from the self-inverse letter, negation of the letter negates the block
  have hnegvec : ∀ a : A, a ≠ hh → vec (neg a) = -vec a := by
    intro a ha
    have hatt : (a : ℕ) ∈ S := a.2
    have hlt := hattlt _ hatt
    funext i
    by_cases h0 : (a : ℕ) = 0
    · -- the zero letter: the block is the zero block
      have hz : ((neg a : A) : ℕ) = 0 := by simp [hnegdef, h0]
      have hc : D.dwCost (rep 0) = 0 := by
        have := (hrep 0 (D.zero_mem_attainableRes k)).2
        rw [this]
        simpa using D.cMinus_zero_eq_zero k
      have hz0 : ∀ j : Fin k, ((rep 0 j : ℤ)) = 0 :=
        fun j => D.eq_zero_of_dwCost_eq_zero (rep 0) hc j
      have hva : vec a i = 0 := by
        simp only [hvecdef, h0]
        simp [hqk.le, hz0 i]
      have hvna : vec (neg a) i = 0 := by
        simp only [hvecdef, hz]
        simp [hqk.le, hz0 i]
      simp [hva, hvna]
    · have h2 : 2 * (a : ℕ) ≠ D.q ^ k := fun h => ha (hhspec a h0 h)
      have hz : ((neg a : A) : ℕ) = D.q ^ k - (a : ℕ) := by simp [hnegdef, h0]
      have hpos : 0 < (a : ℕ) := Nat.pos_of_ne_zero h0
      by_cases hle : 2 * (a : ℕ) ≤ D.q ^ k
      · have hlt2 : 2 * (a : ℕ) < D.q ^ k := lt_of_le_of_ne hle h2
        have hnotle : ¬ (2 * (D.q ^ k - (a : ℕ)) ≤ D.q ^ k) := by omega
        have hback : D.q ^ k - (D.q ^ k - (a : ℕ)) = (a : ℕ) := by omega
        simp only [hvecdef, hz, hnotle, if_false, hback, hle, if_true]
        simp
      · have hnotle : 2 * (D.q ^ k - (a : ℕ)) ≤ D.q ^ k := by omega
        simp only [hvecdef, hz, hnotle, if_true, hle, if_false]
        simp
  -- injectivity of the residues
  have hinj : Function.Injective fun a : A => ((D.blockVal k (vec a) : ℤ) : ZMod (D.q ^ k)) := by
    intro a b hab
    have hmod := (ZMod.intCast_eq_intCast_iff' (D.blockVal k (vec a)) (D.blockVal k (vec b))
      (D.q ^ k)).1 hab
    rw [hqkZ] at hmod
    have h1 := (hkey a).1
    have h2 := (hkey b).1
    have hnn : ((a : ℕ) : ℤ) ≡ ((b : ℕ) : ℤ) [ZMOD (D.q : ℤ) ^ k] :=
      (h1.symm.trans hmod).trans h2
    have hla := hattlt _ a.2
    have hlb := hattlt _ b.2
    refine Subtype.ext ?_
    rw [Int.ModEq, ← hqkZ, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hla),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlb)] at hnn
    exact_mod_cast hnn
  -- both orientations of the self-inverse block have the same residue
  have hhres : ((D.blockVal k (vec hh) : ℤ) : ZMod (D.q ^ k))
      = -((D.blockVal k (vec hh) : ℤ) : ZMod (D.q ^ k)) := by
    have hdvd2 : ((D.q ^ k : ℕ) : ℤ) ∣ 2 * ((hh : ℕ) : ℤ) := by
      rcases hhcase with h0 | h2
      · rw [h0]; simp
      · refine ⟨1, ?_⟩
        have hcast : ((D.q ^ k : ℕ) : ℤ) = 2 * ((hh : ℕ) : ℤ) := by exact_mod_cast h2.symm
        linarith
    have hmodv : D.blockVal k (vec hh) ≡ ((hh : ℕ) : ℤ) [ZMOD (D.q : ℤ) ^ k] := (hkey hh).1
    have hdvd : ((D.q ^ k : ℕ) : ℤ) ∣ D.blockVal k (vec hh) + D.blockVal k (vec hh) := by
      have hd1 : ((D.q ^ k : ℕ) : ℤ) ∣ D.blockVal k (vec hh) - ((hh : ℕ) : ℤ) := by
        rw [hqkZ]
        exact Int.ModEq.dvd hmodv.symm
      have : D.blockVal k (vec hh) + D.blockVal k (vec hh)
          = (D.blockVal k (vec hh) - ((hh : ℕ) : ℤ)) + (D.blockVal k (vec hh) - ((hh : ℕ) : ℤ))
            + 2 * ((hh : ℕ) : ℤ) := by ring
      rw [this]
      exact dvd_add (dvd_add hd1 hd1) hdvd2
    have hz : ((D.blockVal k (vec hh) + D.blockVal k (vec hh) : ℤ) : ZMod (D.q ^ k)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast hdvd)
    push_cast at hz
    linear_combination hz
  -- the oriented core construction
  have hcore := D.core_bound_oriented k hk vec hvec neg hneginv hh hhnegh hnegvec hhres hinj
    x hx0 hx1 Pp C hPp0 hC0 hPp
  -- the alphabet sum is exactly `Z_k(x)`
  have hsumA : (∑ a : A, x ^ D.blockCost k (vec a)) = D.Zminus x k := by
    rw [Zminus, ← hSdef, ← Finset.sum_coe_sort S (fun n : ℕ => x ^ D.cMinus k (n : ℤ))]
    exact Finset.sum_congr rfl fun a _ => by rw [(hkey a).2]
  rwa [hsumA] at hcore

/-- The weaker form of `controlled_block_bound_gen` with `Z_k(x) - 1` in place of `Z_k(x)`,
kept because it is the form in which the passage to the limit of Lemma 4
(`lem:controlled-pressure`) of `masked_digit_bound.tex` is organized here. -/
theorem controlled_block_bound_gen_sub_one (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ)
    (hk : 0 < k) (Pp C : ℝ) (hPp0 : 0 < Pp) (hC0 : 0 < C)
    (hPp : ∀ m T : ℕ, ((D.sumSet m T).card : ℝ) * x ^ T ≤ C * Pp ^ m) :
    1 + (Real.log (D.Zminus x k - 1) / k - Real.log Pp) / Real.log D.q ≤ C3a := by
  have hfull := D.controlled_block_bound_gen x hx0 hx1 k hk Pp C hPp0 hC0 hPp
  have hZpos : 0 < D.Zminus x k - 1 := by
    have := D.one_lt_Zminus hx0 hx1 hk
    linarith
  have hlog : Real.log (D.Zminus x k - 1) ≤ Real.log (D.Zminus x k) :=
    Real.log_le_log hZpos (by linarith)
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hlogq : 0 < Real.log D.q := Real.log_pos (by exact_mod_cast hq1)
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hstep : (Real.log (D.Zminus x k - 1) / k - Real.log Pp) / Real.log D.q
      ≤ (Real.log (D.Zminus x k) / k - Real.log Pp) / Real.log D.q := by gcongr
  linarith

/-- **Proposition 3 (Controlled-carry block bound)** of `masked_digit_bound.tex`,
equation (18) (`eq:controlled-block-bound`), in the form stated in the source, with the
sum-side factor `P₊(x)` and the full block partition sum `Z_k(x)`.  It is the case
`Pp = P₊(x)`, `C = 1` of `controlled_block_bound_gen`. -/
theorem controlled_block_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ) (hk : 0 < k) :
    1 + (Real.log (D.Zminus x k) / k - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a :=
  D.controlled_block_bound_gen x hx0 hx1 k hk (D.Pplus x) 1 (D.Pplus_pos hx0) one_pos
    (fun m T => by simpa using D.sumSet_card_mul_pow_le x hx0 hx1 m T)

/-- The form of Proposition 3 with `Z_k(x) - 1`, used in the passage to the limit of
Lemma 4 (`lem:controlled-pressure`) of `masked_digit_bound.tex`. -/
theorem controlled_block_bound_sub_one (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (k : ℕ)
    (hk : 0 < k) :
    1 + (Real.log (D.Zminus x k - 1) / k - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a :=
  D.controlled_block_bound_gen_sub_one x hx0 hx1 k hk (D.Pplus x) 1 (D.Pplus_pos hx0) one_pos
    (fun m T => by simpa using D.sumSet_card_mul_pow_le x hx0 hx1 m T)


/-! ## The infinite-block pressure -/

/-- The difference-side pressure `𝒫(x) = sup_{k ≥ 1} k⁻¹ log Z_k(x)` of Lemma 4
(`lem:controlled-pressure`) of `masked_digit_bound.tex`. -/
noncomputable def PminusPressure (x : ℝ) : ℝ :=
  sSup ((fun k : ℕ => Real.log (D.Zminus x k) / k) '' Set.Ici 1)

/-- The auxiliary subadditive sequence `-log Z_k(x)` used in the Fekete argument in the proof
of Lemma 4 (`lem:controlled-pressure`) of `masked_digit_bound.tex`. -/
noncomputable def negLogZ (x : ℝ) (k : ℕ) : ℝ := -Real.log (D.Zminus x k)

/-- The sequence `-log Z_k(x)` is subadditive, by supermultiplicativity of `Z_k(x)`; this is
the input to Fekete's lemma in the proof of Lemma 4 (`lem:controlled-pressure`) of
`masked_digit_bound.tex`. -/
theorem subadditive_negLogZ {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : Subadditive (D.negLogZ x) := by
  intro m n
  have hm := D.Zminus_pos hx0 m
  have hn := D.Zminus_pos hx0 n
  have hmn := D.Zminus_pos hx0 (m + n)
  have hle := D.Zminus_supermultiplicative hx0 hx1 m n
  have hlog : Real.log (D.Zminus x m * D.Zminus x n) ≤ Real.log (D.Zminus x (m + n)) :=
    Real.log_le_log (mul_pos hm hn) hle
  rw [Real.log_mul (ne_of_gt hm) (ne_of_gt hn)] at hlog
  simp only [negLogZ]
  linarith

/-- For `k ≥ 1`, `k⁻¹ log Z_k(x) ≤ log q`, since `Z_k(x) ≤ q^k` (Section 4 of
`masked_digit_bound.tex`). -/
theorem logZ_div_le_logq {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (D.Zminus x k) / k ≤ Real.log D.q := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqR : (1 : ℝ) < (D.q : ℝ) := by exact_mod_cast hq1
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h1 : Real.log (D.Zminus x k) ≤ Real.log ((D.q : ℝ) ^ k) :=
    Real.log_le_log (D.Zminus_pos hx0 k) (D.Zminus_le_pow hx0 hx1.le k)
  rw [Real.log_pow] at h1
  rw [div_le_iff₀ hkR]
  linarith

/-- The sequence `k⁻¹ (-log Z_k(x))` is bounded below, the hypothesis needed for Fekete's
lemma in the proof of Lemma 4 (`lem:controlled-pressure`) of `masked_digit_bound.tex`. -/
theorem bddBelow_negLogZ {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    BddBelow (Set.range fun n : ℕ => D.negLogZ x n / n) := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqR : (1 : ℝ) < (D.q : ℝ) := by exact_mod_cast hq1
  have hlogq : 0 < Real.log D.q := Real.log_pos hqR
  refine ⟨-Real.log D.q, ?_⟩
  rintro y ⟨n, rfl⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [negLogZ, D.Zminus_zero, Real.log_one, neg_zero, Nat.cast_zero, div_zero]
    linarith
  · have h := D.logZ_div_le_logq hx0 hx1 hn
    simp only [negLogZ, neg_div]
    linarith

/-- The set of finite-block averages `k⁻¹ log Z_k(x)`, `k ≥ 1`, is bounded above by `log q`;
this makes the supremum defining `𝒫(x)` in Lemma 4 (`lem:controlled-pressure`) of
`masked_digit_bound.tex` well defined. -/
theorem bddAbove_logZ_div {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    BddAbove ((fun k : ℕ => Real.log (D.Zminus x k) / k) '' Set.Ici 1) := by
  refine ⟨Real.log D.q, ?_⟩
  rintro y ⟨k, hk, rfl⟩
  exact D.logZ_div_le_logq hx0 hx1 hk

/-- Each finite block gives a lower bound for the pressure. -/
theorem le_PminusPressure {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {k : ℕ} (hk : 1 ≤ k) :
    Real.log (D.Zminus x k) / k ≤ D.PminusPressure x :=
  le_csSup (D.bddAbove_logZ_div hx0 hx1) ⟨k, hk, rfl⟩

/-- **Existence of the infinite-block pressure**, Lemma 4 (`lem:controlled-pressure`) of
`masked_digit_bound.tex`: `k⁻¹ log Z_k(x)` converges to its supremum, by Fekete's lemma
applied to the superadditive sequence `log Z_k(x)`. -/
theorem tendsto_PminusPressure {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun k : ℕ => Real.log (D.Zminus x k) / k) atTop (𝓝 (D.PminusPressure x)) := by
  have hsub := D.subadditive_negLogZ hx0 hx1
  have hbdd := D.bddBelow_negLogZ hx0 hx1
  have hneg : Tendsto (fun n : ℕ => -(D.negLogZ x n / n)) atTop (𝓝 (-hsub.lim)) :=
    (hsub.tendsto_lim hbdd).neg
  have hfun : (fun k : ℕ => Real.log (D.Zminus x k) / k)
      = fun n : ℕ => -(D.negLogZ x n / n) := by
    funext n; simp [negLogZ, neg_div]
  have heq : D.PminusPressure x = -hsub.lim := by
    refine le_antisymm (csSup_le ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_) ?_
    · rintro y ⟨k, hk, rfl⟩
      have hk1 : 1 ≤ k := hk
      have hk0 : k ≠ 0 := by omega
      have h := hsub.lim_le_div hbdd hk0
      simp only [negLogZ, neg_div] at h
      linarith
    · refine le_of_tendsto hneg ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      have h := D.le_PminusPressure hx0 hx1 hk
      simp only [negLogZ, neg_div, neg_neg]
      exact h
  rw [hfun, heq]
  exact hneg

/-- The passage to the limit in the proof of Lemma 4 (`lem:controlled-pressure`) of
`masked_digit_bound.tex`: if every finite block satisfies `m⁻¹ log Z_m(x) ≤ R`, then the
difference-side pressure `𝒫(x) = sup_m m⁻¹ log Z_m(x)` satisfies `𝒫(x) ≤ R`. -/
theorem PminusPressure_le_of_block_bound_full {x R : ℝ}
    (hbound : ∀ m : ℕ, 0 < m → Real.log (D.Zminus x m) / m ≤ R) :
    D.PminusPressure x ≤ R := by
  refine csSup_le ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
  rintro y ⟨k, hk, rfl⟩
  exact hbound k hk

/-- The variant of `PminusPressure_le_of_block_bound_full` for the weaker block bound with
`Z_m(x) - 1`; the `-1` is absorbed in the limit. -/
theorem PminusPressure_le_of_block_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {R : ℝ}
    (hbound : ∀ m : ℕ, 0 < m → Real.log (D.Zminus x m - 1) / m ≤ R) :
    D.PminusPressure x ≤ R := by
  have hA : ∀ k : ℕ, 1 ≤ k → Real.log (D.Zminus x k) ≤ (k : ℝ) * R := by
    intro k hk
    have hZk1 : 1 < D.Zminus x k := D.one_lt_Zminus hx0 hx1 hk
    have hkey : ∀ n : ℕ, 1 ≤ n → 2 ≤ (D.Zminus x k) ^ n →
        Real.log (D.Zminus x k) ≤ (k : ℝ) * R + Real.log 2 / n := by
      intro n hn h2
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hcast : ((n * k : ℕ) : ℝ) = (n : ℝ) * (k : ℝ) := by push_cast; ring
      have hdiv : Real.log (D.Zminus x (n * k) - 1) / ((n : ℝ) * (k : ℝ)) ≤ R := by
        rw [← hcast]; exact hbound (n * k) (by positivity)
      rw [div_le_iff₀ (by positivity)] at hdiv
      -- lower bound for `log (Z_{nk} - 1)`
      have hpow : (D.Zminus x k) ^ n ≤ D.Zminus x (n * k) := D.Zminus_pow_le hx0 hx1 k n
      have hhalf : (D.Zminus x k) ^ n / 2 ≤ D.Zminus x (n * k) - 1 := by linarith
      have hlow : Real.log ((D.Zminus x k) ^ n / 2) ≤ Real.log (D.Zminus x (n * k) - 1) :=
        Real.log_le_log (by positivity) hhalf
      rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlow
      have hgoal : (n : ℝ) * Real.log (D.Zminus x k)
          ≤ (n : ℝ) * ((k : ℝ) * R + Real.log 2 / n) := by
        have hcan : (n : ℝ) * (Real.log 2 / n) = Real.log 2 := by field_simp
        rw [mul_add, hcan]
        nlinarith [hlow, hdiv]
      exact le_of_mul_le_mul_left hgoal hnpos
    have hlim : Tendsto (fun n : ℕ => (k : ℝ) * R + Real.log 2 / n) atTop (𝓝 ((k : ℝ) * R)) := by
      simpa using
        (tendsto_const_nhds (x := (k : ℝ) * R) (f := atTop (α := ℕ))).add
          (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_pow_atTop_atTop_of_one_lt hZk1).eventually_ge_atTop 2] with n hn h2
    exact hkey n hn h2
  refine csSup_le ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
  rintro y ⟨k, hk, rfl⟩
  have hk1 : 1 ≤ k := hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  rw [div_le_iff₀ hkpos]
  have := hA k hk1
  linarith

/-- **Lemma 4 (Infinite-block pressure)** of `masked_digit_bound.tex`, equation (21)
(`eq:controlled-limit-bound`): `C₃ₐ ≥ 1 + (𝒫(x) - log P₊(x)) / log q`. -/
theorem controlled_pressure_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    1 + (D.PminusPressure x - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hlogq : 0 < Real.log D.q := Real.log_pos (by exact_mod_cast hq1)
  have hB : D.PminusPressure x ≤ Real.log (D.Pplus x) + (C3a - 1) * Real.log D.q := by
    refine D.PminusPressure_le_of_block_bound_full (fun m hm => ?_)
    have hblock := D.controlled_block_bound x hx0 hx1 m hm
    have h1 : (Real.log (D.Zminus x m) / (m : ℝ)
        - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a - 1 := by linarith
    rw [div_le_iff₀ hlogq] at h1
    linarith
  have hfin : (D.PminusPressure x - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a - 1 := by
    rw [div_le_iff₀ hlogq]
    linarith
  linarith

end MaskData

end MaskedDigit
