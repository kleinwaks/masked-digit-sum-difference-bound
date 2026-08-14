import RequestProject.ControlledDifference

/-!
# Exact pressure for distinct sum outputs

This file formalizes Section 4.1 ("Exact pressure for distinct sums") and Proposition 5
("Two-sided carry pressure") of `masked_digit_bound.tex`.

The factor `P₊(x)` of Section 2 counts sum-digit words even when several words produce the
same integer after carrying.  Here all representations of the same output integer are
combined before counting:

* `sumOutputs l` is the set of distinct integers produced by `l` sum digits;
* `cPlus l y` is the minimum digit cost producing the output `y`;
* `Wplus x l = ∑_y x^{cPlus l y}` is the quantity `W_ℓ(x)` of the source;
* `Wplus_almost_multiplicative` is equation (28) (`eq:sum-almost-multiplicative`);
* `PplusPressure` is `𝒫₊(x) = inf_ℓ ℓ⁻¹ log W_ℓ(x)`, and
  `finite_sum_pressure_error` is equation (27) (`eq:sum-pressure-error`);
* `two_block_bound`, `ultimate_bound` and `finite_pressure_certificate` are equations (25),
  (24) and (26) of Proposition 5.
-/

open scoped BigOperators
open Filter Topology

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-! ## Sum words and their outputs -/

/-- A sum word of length `l`: an `l`-tuple of digits from the sum support `S = M + M`. -/
abbrev SumWord (l : ℕ) := Fin l → {s : ℕ // s ∈ D.sumSupport}

/-- Sum words are never absent: the all-zero word exists, since `0 ∈ M + M`. -/
instance instNonemptySumWord (l : ℕ) : Nonempty (D.SumWord l) :=
  ⟨fun _ => ⟨0, D.zero_mem_sumSupport⟩⟩

/-- The integer value `∑ᵢ sᵢ qⁱ` of a sum word. -/
def swValue {l : ℕ} (w : D.SumWord l) : ℕ := ∑ i, (w i : ℕ) * D.q ^ (i : ℕ)

/-- The total digit cost `∑ᵢ sᵢ` of a sum word. -/
def swCost {l : ℕ} (w : D.SumWord l) : ℕ := ∑ i, (w i : ℕ)

/-- The set of distinct integer outputs of `l` sum digits, as in Section 4.1 of
`masked_digit_bound.tex`. -/
noncomputable def sumOutputs (l : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (D.SumWord l)).image D.swValue

/-- The minimum cost `c⁺_ℓ(y)` of producing the output integer `y` with `l` sum digits;
this is the quantity combined over all representations in Section 4.1 of
`masked_digit_bound.tex`. -/
noncomputable def cPlus (l : ℕ) (y : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ w : D.SumWord l, D.swValue w = y ∧ D.swCost w = c}

/-- `W_ℓ(x)`, the sum, over the distinct integer outputs of `l` sum digits, of `x` raised to
the minimum cost of producing that output (Section 4.1 of `masked_digit_bound.tex`). -/
noncomputable def Wplus (x : ℝ) (l : ℕ) : ℝ :=
  ∑ y ∈ D.sumOutputs l, x ^ D.cPlus l y

/-! ### Elementary properties of sum words -/

theorem mem_sumOutputs {l : ℕ} {y : ℕ} :
    y ∈ D.sumOutputs l ↔ ∃ w : D.SumWord l, D.swValue w = y := by
  simp [sumOutputs]

/-- The value of a sum word is one of the distinct outputs counted by `W_ℓ(x)` in Section 4.1 of `masked_digit_bound.tex`. -/
theorem swValue_mem_sumOutputs {l : ℕ} (w : D.SumWord l) : D.swValue w ∈ D.sumOutputs l :=
  D.mem_sumOutputs.2 ⟨w, rfl⟩

/-- `c⁺_ℓ` never exceeds the cost of any word producing the given output. -/
theorem cPlus_le {l : ℕ} (w : D.SumWord l) : D.cPlus l (D.swValue w) ≤ D.swCost w :=
  Nat.sInf_le ⟨w, rfl, rfl⟩

/-- A minimum-cost word exists for every attained output. -/
theorem exists_swCost_eq_cPlus {l y : ℕ} (hy : y ∈ D.sumOutputs l) :
    ∃ w : D.SumWord l, D.swValue w = y ∧ D.swCost w = D.cPlus l y := by
  obtain ⟨w, hw⟩ := D.mem_sumOutputs.1 hy
  have hne : {c : ℕ | ∃ w : D.SumWord l, D.swValue w = y ∧ D.swCost w = c}.Nonempty :=
    ⟨D.swCost w, w, hw, rfl⟩
  obtain ⟨w', hw', hc⟩ := Nat.sInf_mem hne
  exact ⟨w', hw', hc⟩

/-- The all-zero sum word. -/
def swZero (l : ℕ) : D.SumWord l := fun _ => ⟨0, D.zero_mem_sumSupport⟩

/-- The all-zero sum word has value `0`. -/
theorem swValue_swZero (l : ℕ) : D.swValue (D.swZero l) = 0 := by
  simp [swValue, swZero]

/-- The all-zero sum word has digit cost `0`. -/
theorem swCost_swZero (l : ℕ) : D.swCost (D.swZero l) = 0 := by
  simp [swCost, swZero]

/-- The output `0` is always attained, so the output set of Section 4.1 of `masked_digit_bound.tex` is nonempty. -/
theorem zero_mem_sumOutputs (l : ℕ) : 0 ∈ D.sumOutputs l := by
  rw [← D.swValue_swZero l]
  exact D.swValue_mem_sumOutputs _

/-- The minimum cost `c⁺_ℓ(0)` of the zero output vanishes, so the term `x^0 = 1` occurs in `W_ℓ(x)`. -/
theorem cPlus_zero_eq_zero (l : ℕ) : D.cPlus l 0 = 0 := by
  have h := D.cPlus_le (D.swZero l)
  rw [D.swValue_swZero, D.swCost_swZero] at h
  omega

/-- The set of distinct sum outputs of Section 4.1 of `masked_digit_bound.tex` is nonempty. -/
theorem sumOutputs_nonempty (l : ℕ) : (D.sumOutputs l).Nonempty :=
  ⟨0, D.zero_mem_sumOutputs l⟩

/-- Every output of `l` sum digits is less than `2 q^l`, since every sum digit is at most
`2B ≤ 2(q-1)`.  This is the reason why, in Section 4.1 of `masked_digit_bound.tex`, only two
internal carries can occur at a block boundary. -/
theorem swValue_lt {l : ℕ} (w : D.SumWord l) : D.swValue w < 2 * D.q ^ l := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have key : ∀ (m : ℕ) (a : Fin m → ℕ), (∀ i, a i ≤ 2 * (D.q - 1)) →
      (∑ i, a i * D.q ^ (i : ℕ)) + 2 ≤ 2 * D.q ^ m := by
    intro m
    induction m with
    | zero => intro a _; simp
    | succ n ih =>
      intro a ha
      rw [Fin.sum_univ_castSucc]
      have h1 := ih (fun i => a i.castSucc) (fun i => ha _)
      have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
      have h2 : a (Fin.last n) * D.q ^ ((Fin.last n : Fin (n+1)) : ℕ)
          ≤ 2 * (D.q - 1) * D.q ^ n := by
        rw [hlast]
        exact Nat.mul_le_mul_right _ (ha _)
      have h3 : 2 * (D.q - 1) * D.q ^ n + 2 * D.q ^ n = 2 * D.q ^ (n + 1) := by
        have : D.q - 1 + 1 = D.q := by omega
        rw [pow_succ]
        calc 2 * (D.q - 1) * D.q ^ n + 2 * D.q ^ n = 2 * ((D.q - 1) + 1) * D.q ^ n := by ring
          _ = 2 * (D.q ^ n * D.q) := by rw [this]; ring
      simp only [Fin.val_castSucc] at h1 ⊢
      omega
  have hd : ∀ i, (w i : ℕ) ≤ 2 * (D.q - 1) := by
    intro i
    have h1 := D.le_of_mem_sumSupport (w i).2
    have h2 := D.q_gt_B
    omega
  have h : D.swValue w + 2 ≤ 2 * D.q ^ l := key l (fun i => (w i : ℕ)) hd
  omega

/-! ### Positivity and the value at `ℓ = 0` -/

theorem Wplus_pos {x : ℝ} (hx : 0 < x) (l : ℕ) : 0 < D.Wplus x l := by
  refine Finset.sum_pos (fun y _ => pow_pos hx _) (D.sumOutputs_nonempty l)

/-- `W₀(x) = 1`. -/
theorem Wplus_zero {x : ℝ} : D.Wplus x 0 = 1 := by
  have h1 : D.sumOutputs 0 = {0} := by
    ext y
    simp only [D.mem_sumOutputs, Finset.mem_singleton]
    constructor
    · rintro ⟨w, rfl⟩; simp [swValue]
    · rintro rfl; exact ⟨D.swZero 0, D.swValue_swZero 0⟩
  simp [Wplus, h1, D.cPlus_zero_eq_zero]

/-- `W_ℓ(x) ≥ 1`, since the output `0` has cost `0`. -/
theorem one_le_Wplus {x : ℝ} (hx : 0 < x) (l : ℕ) : 1 ≤ D.Wplus x l := by
  classical
  have hsub : ({0} : Finset ℕ) ⊆ D.sumOutputs l := by
    intro y hy
    rw [Finset.mem_singleton] at hy
    subst hy
    exact D.zero_mem_sumOutputs l
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun y => x ^ D.cPlus l y) hsub
    (fun y _ _ => (pow_pos hx _).le)
  simpa [D.cPlus_zero_eq_zero, Wplus] using h

/-! ### Splitting and concatenating sum words -/

/-- Concatenation of two sum words. -/
def swAppend {r s : ℕ} (u : D.SumWord r) (v : D.SumWord s) : D.SumWord (r + s) :=
  Fin.append u v

/-- Concatenating two sum blocks adds their values with the base shift `q^r`; this is the block decomposition used for equation (28) of `masked_digit_bound.tex`. -/
theorem swValue_append {r s : ℕ} (u : D.SumWord r) (v : D.SumWord s) :
    D.swValue (D.swAppend u v) = D.swValue u + D.q ^ r * D.swValue v := by
  simp only [swValue, swAppend]
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by simp [Fin.append_left]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.natAdd r i : Fin (r + s)) : ℕ) = r + (i : ℕ) := rfl
    simp only [Fin.append_right, hi, pow_add]
    ring

/-- Concatenating two sum blocks adds their digit costs. -/
theorem swCost_append {r s : ℕ} (u : D.SumWord r) (v : D.SumWord s) :
    D.swCost (D.swAppend u v) = D.swCost u + D.swCost v := by
  simp only [swCost, swAppend]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- The first block of a word of length `r + s`. -/
def swLeft {r s : ℕ} (w : D.SumWord (r + s)) : D.SumWord r := fun i => w (Fin.castAdd s i)

/-- The second block of a word of length `r + s`. -/
def swRight {r s : ℕ} (w : D.SumWord (r + s)) : D.SumWord s := fun i => w (Fin.natAdd r i)

/-- Splitting a sum word into its two blocks and concatenating them again gives back the word. -/
theorem swAppend_swLeft_swRight {r s : ℕ} (w : D.SumWord (r + s)) :
    D.swAppend (D.swLeft w) (D.swRight w) = w :=
  Fin.append_castAdd_natAdd

/-- The value of a sum word of length `r + s` splits as `value(left) + q^r · value(right)`, the block factorization behind equation (28) of `masked_digit_bound.tex`. -/
theorem swValue_split {r s : ℕ} (w : D.SumWord (r + s)) :
    D.swValue w = D.swValue (D.swLeft w) + D.q ^ r * D.swValue (D.swRight w) := by
  calc D.swValue w = D.swValue (D.swAppend (D.swLeft w) (D.swRight w)) := by
        rw [D.swAppend_swLeft_swRight]
    _ = _ := D.swValue_append _ _

/-- The digit cost of a sum word of length `r + s` is the sum of the costs of its two blocks. -/
theorem swCost_split {r s : ℕ} (w : D.SumWord (r + s)) :
    D.swCost w = D.swCost (D.swLeft w) + D.swCost (D.swRight w) := by
  calc D.swCost w = D.swCost (D.swAppend (D.swLeft w) (D.swRight w)) := by
        rw [D.swAppend_swLeft_swRight]
    _ = _ := D.swCost_append _ _

/-! ### Almost multiplicativity -/

/-- The minimum cost of a concatenated output is at most the sum of the two minimum costs. -/
theorem cPlus_append_le {r s : ℕ} {a b : ℕ} (ha : a ∈ D.sumOutputs r) (hb : b ∈ D.sumOutputs s) :
    D.cPlus (r + s) (a + D.q ^ r * b) ≤ D.cPlus r a + D.cPlus s b := by
  obtain ⟨u, hu, hcu⟩ := D.exists_swCost_eq_cPlus ha
  obtain ⟨v, hv, hcv⟩ := D.exists_swCost_eq_cPlus hb
  have h := D.cPlus_le (D.swAppend u v)
  rw [D.swValue_append, D.swCost_append, hu, hv, hcu, hcv] at h
  exact h

/-- The concatenation of two attained outputs is an attained output of the concatenated length. -/
theorem mem_sumOutputs_append {r s : ℕ} {a b : ℕ} (ha : a ∈ D.sumOutputs r)
    (hb : b ∈ D.sumOutputs s) : a + D.q ^ r * b ∈ D.sumOutputs (r + s) := by
  obtain ⟨u, hu⟩ := D.mem_sumOutputs.1 ha
  obtain ⟨v, hv⟩ := D.mem_sumOutputs.1 hb
  refine D.mem_sumOutputs.2 ⟨D.swAppend u v, ?_⟩
  rw [D.swValue_append, hu, hv]

/-- **Equation (28) (`eq:sum-almost-multiplicative`) of `masked_digit_bound.tex`:**
`W_{r+s}(x) ≤ W_r(x) W_s(x) ≤ 2 W_{r+s}(x)`.  The proof in the source splits a canonical
output word at the block boundary; the weight of a concatenated output is the maximum over
the two possible internal carries, while the two-state matrix product is their sum. -/
theorem Wplus_almost_multiplicative (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (r s : ℕ) :
    D.Wplus x (r + s) ≤ D.Wplus x r * D.Wplus x s ∧
      D.Wplus x r * D.Wplus x s ≤ 2 * D.Wplus x (r + s) := by
  classical
  have hq0 : 0 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hprod : D.Wplus x r * D.Wplus x s
      = ∑ p ∈ (D.sumOutputs r) ×ˢ (D.sumOutputs s), x ^ (D.cPlus r p.1 + D.cPlus s p.2) := by
    rw [Finset.sum_product, Wplus, Wplus, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (pow_add x _ _).symm
  constructor
  · -- `W_{r+s} ≤ W_r W_s` : split the minimum-cost word of each output
    have key : ∀ y : ℕ, ∃ p : ℕ × ℕ, y ∈ D.sumOutputs (r + s) →
        (p.1 ∈ D.sumOutputs r ∧ p.2 ∈ D.sumOutputs s ∧ y = p.1 + D.q ^ r * p.2 ∧
          D.cPlus r p.1 + D.cPlus s p.2 ≤ D.cPlus (r + s) y) := by
      intro y
      by_cases hy : y ∈ D.sumOutputs (r + s)
      · obtain ⟨w, hw, hc⟩ := D.exists_swCost_eq_cPlus hy
        refine ⟨(D.swValue (D.swLeft w), D.swValue (D.swRight w)), fun _ =>
          ⟨D.swValue_mem_sumOutputs _, D.swValue_mem_sumOutputs _, ?_, ?_⟩⟩
        · rw [← hw]; exact D.swValue_split w
        · dsimp only
          have h1 := D.cPlus_le (D.swLeft w)
          have h2 := D.cPlus_le (D.swRight w)
          have h3 := D.swCost_split w
          omega
      · exact ⟨(0, 0), fun hy' => absurd hy' hy⟩
    choose G hG using key
    have hinjG : Set.InjOn G ↑(D.sumOutputs (r + s)) := by
      intro y hy y' hy' hgg
      rw [(hG y hy).2.2.1, (hG y' hy').2.2.1, hgg]
    calc D.Wplus x (r + s) = ∑ y ∈ D.sumOutputs (r + s), x ^ D.cPlus (r + s) y := rfl
      _ ≤ ∑ y ∈ D.sumOutputs (r + s), x ^ (D.cPlus r (G y).1 + D.cPlus s (G y).2) :=
          Finset.sum_le_sum fun y hy =>
            pow_le_pow_of_le_one hx0.le hx1.le (hG y hy).2.2.2
      _ = ∑ p ∈ (D.sumOutputs (r + s)).image G, x ^ (D.cPlus r p.1 + D.cPlus s p.2) :=
          (Finset.sum_image (f := fun p : ℕ × ℕ => x ^ (D.cPlus r p.1 + D.cPlus s p.2))
            (g := G) hinjG).symm
      _ ≤ ∑ p ∈ (D.sumOutputs r) ×ˢ (D.sumOutputs s), x ^ (D.cPlus r p.1 + D.cPlus s p.2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => (pow_pos hx0 _).le)
          intro p hp
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨(hG y hy).1, (hG y hy).2.1⟩
      _ = D.Wplus x r * D.Wplus x s := hprod.symm
  · -- `W_r W_s ≤ 2 W_{r+s}` : the concatenation map is at most two-to-one
    set h : ℕ × ℕ → ℕ := fun p => p.1 + D.q ^ r * p.2 with hhdef
    have hmaps : ∀ p ∈ (D.sumOutputs r) ×ˢ (D.sumOutputs s), h p ∈ D.sumOutputs (r + s) := by
      intro p hp
      rw [Finset.mem_product] at hp
      exact D.mem_sumOutputs_append hp.1 hp.2
    have hfiber : ∀ y : ℕ,
        (((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y)).card ≤ 2 := by
      intro y
      have hqr : 0 < D.q ^ r := pow_pos hq0 r
      have hmem : ∀ p ∈ ((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y),
          y = p.1 + D.q ^ r * p.2 ∧ p.1 < 2 * D.q ^ r := by
        intro p hp
        rw [Finset.mem_filter, Finset.mem_product] at hp
        obtain ⟨⟨hp1, hp2⟩, hpy⟩ := hp
        obtain ⟨u, hu⟩ := D.mem_sumOutputs.1 hp1
        refine ⟨hpy.symm, ?_⟩
        rw [← hu]
        exact D.swValue_lt u
      have hb : Set.MapsTo (fun p : ℕ × ℕ => p.2)
          ↑(((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y))
          ↑(Finset.Icc (y / D.q ^ r - 1) (y / D.q ^ r)) := by
        intro p hp
        obtain ⟨hy, hlt⟩ := hmem p (by simpa using hp)
        have hle : p.2 ≤ y / D.q ^ r := by
          rw [Nat.le_div_iff_mul_le hqr, mul_comm, hy]
          exact Nat.le_add_left _ _
        have hge : y / D.q ^ r ≤ p.2 + 1 := by
          rw [Nat.div_le_iff_le_mul_add_pred hqr, hy]
          have hmul : D.q ^ r * (p.2 + 1) = D.q ^ r * p.2 + D.q ^ r := by ring
          omega
        simp only [Finset.coe_Icc, Set.mem_Icc]
        omega
      have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2)
          ↑(((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y)) := by
        intro p hp p' hp' h22
        obtain ⟨hy, -⟩ := hmem p (by simpa using hp)
        obtain ⟨hy', -⟩ := hmem p' (by simpa using hp')
        have h22' : p.2 = p'.2 := h22
        refine Prod.ext ?_ h22'
        rw [h22'] at hy
        omega
      have hcard := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2) hb hinj
      have h2 : (Finset.Icc (y / D.q ^ r - 1) (y / D.q ^ r)).card ≤ 2 := by
        rw [Nat.card_Icc]
        omega
      omega
    calc D.Wplus x r * D.Wplus x s
        = ∑ p ∈ (D.sumOutputs r) ×ˢ (D.sumOutputs s), x ^ (D.cPlus r p.1 + D.cPlus s p.2) := hprod
      _ ≤ ∑ p ∈ (D.sumOutputs r) ×ˢ (D.sumOutputs s), x ^ D.cPlus (r + s) (h p) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_product] at hp
          exact pow_le_pow_of_le_one hx0.le hx1.le (D.cPlus_append_le hp.1 hp.2)
      _ = ∑ y ∈ D.sumOutputs (r + s),
            ∑ p ∈ ((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y),
              x ^ D.cPlus (r + s) (h p) :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ y ∈ D.sumOutputs (r + s), 2 * x ^ D.cPlus (r + s) y := by
          refine Finset.sum_le_sum fun y _ => ?_
          have hconst : ∑ p ∈ ((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y),
              x ^ D.cPlus (r + s) (h p)
              = (((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y)).card *
                x ^ D.cPlus (r + s) y := by
            rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
              Finset.sum_const, nsmul_eq_mul]
          rw [hconst]
          have hc : ((((D.sumOutputs r) ×ˢ (D.sumOutputs s)).filter (fun p => h p = y)).card : ℝ)
              ≤ 2 := by exact_mod_cast hfiber y
          exact mul_le_mul_of_nonneg_right hc (pow_pos hx0 _).le
      _ = 2 * D.Wplus x (r + s) := by rw [Wplus, Finset.mul_sum]

/-- The submultiplicative half of equation (28) (`eq:sum-almost-multiplicative`) of `masked_digit_bound.tex`. -/
theorem Wplus_submultiplicative (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (r s : ℕ) :
    D.Wplus x (r + s) ≤ D.Wplus x r * D.Wplus x s :=
  (D.Wplus_almost_multiplicative x hx0 hx1 r s).1

/-! ## The sum-side pressure -/

/-- The sum-side pressure `𝒫₊(x) = inf_{ℓ ≥ 1} ℓ⁻¹ log W_ℓ(x)` of Proposition 5 of
`masked_digit_bound.tex`. -/
noncomputable def PplusPressure (x : ℝ) : ℝ :=
  sInf ((fun l : ℕ => Real.log (D.Wplus x l) / l) '' Set.Ici 1)

/-- `log W_ℓ(x) ≥ 0`, since `W_ℓ(x) ≥ 1`; used for the pressure infimum of Proposition 5 of `masked_digit_bound.tex`. -/
theorem log_Wplus_nonneg {x : ℝ} (hx : 0 < x) (l : ℕ) : 0 ≤ Real.log (D.Wplus x l) :=
  Real.log_nonneg (D.one_le_Wplus hx l)

/-- The quotients `ℓ⁻¹ log W_ℓ(x)` are bounded below by `0`, so the infimum defining `𝒫₊(x)` in Proposition 5 of `masked_digit_bound.tex` exists. -/
theorem bddBelow_logW_div {x : ℝ} (hx0 : 0 < x) :
    BddBelow ((fun l : ℕ => Real.log (D.Wplus x l) / l) '' Set.Ici 1) := by
  refine ⟨0, ?_⟩
  rintro y ⟨l, hl, rfl⟩
  exact div_nonneg (D.log_Wplus_nonneg hx0 l) (Nat.cast_nonneg l)

/-- Every finite block gives an upper bound `𝒫₊(x) ≤ ℓ⁻¹ log W_ℓ(x)`; this is the form in which the `8192`-digit computation of Section 4.3 of `masked_digit_bound.tex` is used. -/
theorem PplusPressure_le {x : ℝ} (hx0 : 0 < x) {l : ℕ} (hl : 1 ≤ l) :
    D.PplusPressure x ≤ Real.log (D.Wplus x l) / l :=
  csInf_le (D.bddBelow_logW_div hx0) ⟨l, hl, rfl⟩

/-- The sum-side pressure `𝒫₊(x)` of Proposition 5 of `masked_digit_bound.tex` is nonnegative. -/
theorem PplusPressure_nonneg {x : ℝ} (hx0 : 0 < x) : 0 ≤ D.PplusPressure x := by
  refine le_csInf ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
  rintro y ⟨l, hl, rfl⟩
  exact div_nonneg (D.log_Wplus_nonneg hx0 l) (Nat.cast_nonneg l)

/-- The sequence `log W_ℓ(x)` is subadditive, by `Wplus_almost_multiplicative`. -/
theorem subadditive_logW {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Subadditive (fun l : ℕ => Real.log (D.Wplus x l)) := by
  intro m n
  have hm := D.Wplus_pos hx0 m
  have hn := D.Wplus_pos hx0 n
  have hle := D.Wplus_submultiplicative x hx0 hx1 m n
  have hlog : Real.log (D.Wplus x (m + n)) ≤ Real.log (D.Wplus x m * D.Wplus x n) :=
    Real.log_le_log (D.Wplus_pos hx0 (m + n)) hle
  rwa [Real.log_mul (ne_of_gt hm) (ne_of_gt hn)] at hlog

/-- The full range of `ℓ⁻¹ log W_ℓ(x)` is bounded below, the hypothesis needed for Fekete’s lemma in Proposition 5 of `masked_digit_bound.tex`. -/
theorem bddBelow_logW_range {x : ℝ} (hx0 : 0 < x) :
    BddBelow (Set.range fun l : ℕ => Real.log (D.Wplus x l) / l) := by
  refine ⟨0, ?_⟩
  rintro y ⟨l, rfl⟩
  exact div_nonneg (D.log_Wplus_nonneg hx0 l) (Nat.cast_nonneg l)

/-- The infimum defining `𝒫₊(x)` is a limit, by Fekete's lemma applied to the subadditive
sequence `log W_ℓ(x)` (Proposition 5 of `masked_digit_bound.tex`). -/
theorem tendsto_PplusPressure {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun l : ℕ => Real.log (D.Wplus x l) / l) atTop (𝓝 (D.PplusPressure x)) := by
  have hsub := D.subadditive_logW hx0 hx1
  have hbdd := D.bddBelow_logW_range hx0
  have heq : D.PplusPressure x = hsub.lim := by
    rw [Subadditive.lim, PplusPressure]
  rw [heq]
  exact hsub.tendsto_lim hbdd

/-- Iterated submultiplicativity with the factor `2`: `W_ℓ(x)^{n+1} ≤ 2ⁿ W_{(n+1)ℓ}(x)`. -/
theorem Wplus_pow_le (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (l n : ℕ) :
    D.Wplus x l ^ (n + 1) ≤ 2 ^ n * D.Wplus x ((n + 1) * l) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 := (D.Wplus_almost_multiplicative x hx0 hx1 ((n + 1) * l) l).2
    have hWl : 0 < D.Wplus x l := D.Wplus_pos hx0 l
    have hstep : D.Wplus x l ^ (n + 1) * D.Wplus x l
        ≤ 2 ^ n * D.Wplus x ((n + 1) * l) * D.Wplus x l :=
      mul_le_mul_of_nonneg_right ih hWl.le
    have hidx : (n + 1 + 1) * l = (n + 1) * l + l := by ring
    have hpos : (0 : ℝ) ≤ 2 ^ n := by positivity
    calc D.Wplus x l ^ (n + 1 + 1) = D.Wplus x l ^ (n + 1) * D.Wplus x l := by ring
      _ ≤ 2 ^ n * (D.Wplus x ((n + 1) * l) * D.Wplus x l) := by nlinarith
      _ ≤ 2 ^ n * (2 * D.Wplus x ((n + 1) * l + l)) := by
          exact mul_le_mul_of_nonneg_left h2 hpos
      _ = 2 ^ (n + 1) * D.Wplus x ((n + 1 + 1) * l) := by rw [hidx]; ring

/-- **Equation (27) (`eq:sum-pressure-error`) of `masked_digit_bound.tex`:**
`0 ≤ ℓ⁻¹ log W_ℓ(x) - 𝒫₊(x) ≤ log 2 / ℓ`. -/
theorem finite_sum_pressure_error (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (l : ℕ) (hl : 0 < l) :
    0 ≤ Real.log (D.Wplus x l) / l - D.PplusPressure x ∧
      Real.log (D.Wplus x l) / l - D.PplusPressure x ≤ Real.log 2 / l := by
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  refine ⟨by linarith [D.PplusPressure_le hx0 hl], ?_⟩
  -- lower bound for the pressure along the subsequence `(n+1) * l`
  have hkey : ∀ n : ℕ, Real.log (D.Wplus x l) / l - Real.log 2 / l
      ≤ Real.log (D.Wplus x ((n + 1) * l)) / (((n + 1) * l : ℕ) : ℝ) := by
    intro n
    have hpow := D.Wplus_pow_le x hx0 hx1 l n
    have hWl : 0 < D.Wplus x l := D.Wplus_pos hx0 l
    have hlog : Real.log (D.Wplus x l ^ (n + 1)) ≤ Real.log (2 ^ n * D.Wplus x ((n + 1) * l)) :=
      Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_mul (by positivity) (ne_of_gt (D.Wplus_pos hx0 _)),
      Real.log_pow] at hlog
    have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
    have hcast : (((n + 1) * l : ℕ) : ℝ) = ((n : ℝ) + 1) * (l : ℝ) := by push_cast; ring
    rw [hcast, div_sub_div_same, div_le_div_iff₀ hlR (by positivity)]
    push_cast at hlog
    nlinarith [hlog, hlR, hlog2, hnR]
  have hlim : Tendsto (fun n : ℕ => Real.log (D.Wplus x ((n + 1) * l)) / (((n + 1) * l : ℕ) : ℝ))
      atTop (𝓝 (D.PplusPressure x)) := by
    have htend := D.tendsto_PplusPressure hx0 hx1
    have hmap : Tendsto (fun n : ℕ => (n + 1) * l) atTop atTop := by
      refine Filter.tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => ?_) Filter.tendsto_id
      calc n = n * 1 := by ring
        _ ≤ (n + 1) * l := Nat.mul_le_mul (Nat.le_succ n) hl
    exact htend.comp hmap
  have hbound : Real.log (D.Wplus x l) / l - Real.log 2 / l ≤ D.PplusPressure x :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hkey)
  linarith

/-! ## The two-sided carry bounds -/

/-- Every element of the digit-bounded sum set has minimum sum cost at most `T`, whence the
weighted bound `|sumSet m T| x^T ≤ W_m(x)` used in the proof of Proposition 5 of
`masked_digit_bound.tex`. -/
theorem sumSet_card_mul_pow_le_Wplus (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (m T : ℕ) :
    ((D.sumSet m T).card : ℝ) * x ^ T ≤ D.Wplus x m := by
  classical
  have hsub : D.sumSet m T ⊆ D.sumOutputs m := by
    intro y hy
    simp only [sumSet, Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨a, ⟨-, -⟩, rfl⟩ := hy
    exact D.mem_sumOutputs.2 ⟨a, rfl⟩
  have hcost : ∀ y ∈ D.sumSet m T, D.cPlus m y ≤ T := by
    intro y hy
    simp only [sumSet, Finset.mem_image, Finset.mem_filter] at hy
    obtain ⟨a, ⟨-, haT⟩, rfl⟩ := hy
    have h := D.cPlus_le (l := m) a
    have : D.swCost a ≤ T := haT
    have hv : D.swValue a = D.flatInt m (fun t => (a t : ℕ)) := rfl
    rw [hv] at h
    omega
  calc ((D.sumSet m T).card : ℝ) * x ^ T = ∑ _y ∈ D.sumSet m T, x ^ T := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ y ∈ D.sumSet m T, x ^ D.cPlus m y := by
        refine Finset.sum_le_sum fun y hy => ?_
        exact pow_le_pow_of_le_one hx0.le hx1.le (hcost y hy)
    _ ≤ ∑ y ∈ D.sumOutputs m, x ^ D.cPlus m y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => (pow_pos hx0 _).le)
    _ = D.Wplus x m := rfl

/-- Iterated submultiplicativity in the form `W_{a·l+b}(x) ≤ W_l(x)^a · W_b(x)`. -/
theorem Wplus_mul_add_le (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (l b : ℕ) :
    ∀ a : ℕ, D.Wplus x (a * l + b) ≤ D.Wplus x l ^ a * D.Wplus x b := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := D.Wplus_submultiplicative x hx0 hx1 l (a * l + b)
    have hidx : (a + 1) * l + b = l + (a * l + b) := by ring
    have hWl : 0 < D.Wplus x l := D.Wplus_pos hx0 l
    calc D.Wplus x ((a + 1) * l + b) = D.Wplus x (l + (a * l + b)) := by rw [hidx]
      _ ≤ D.Wplus x l * D.Wplus x (a * l + b) := h1
      _ ≤ D.Wplus x l * (D.Wplus x l ^ a * D.Wplus x b) :=
          mul_le_mul_of_nonneg_left ih hWl.le
      _ = D.Wplus x l ^ (a + 1) * D.Wplus x b := by ring

/-- **Equation (25) (`eq:finite-two-block-bound`) of `masked_digit_bound.tex`:** for all
`k, l ≥ 1`, `C₃ₐ ≥ 1 + (k⁻¹ log Z_k(x) - ℓ⁻¹ log W_ℓ(x)) / log q`, with the full block
partition sum `Z_k(x)`. -/
theorem two_block_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (k l : ℕ) (hk : 0 < k)
    (hl : 0 < l) :
    1 + (Real.log (D.Zminus x k) / k - Real.log (D.Wplus x l) / l) / Real.log D.q ≤ C3a := by
  classical
  set Pp : ℝ := Real.exp (Real.log (D.Wplus x l) / l) with hPpdef
  have hPp0 : 0 < Pp := Real.exp_pos _
  have hPplog : Real.log Pp = Real.log (D.Wplus x l) / l := Real.log_exp _
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hPp1 : 1 ≤ Pp := by
    rw [hPpdef, Real.one_le_exp_iff]
    exact div_nonneg (D.log_Wplus_nonneg hx0 l) (Nat.cast_nonneg l)
  set C : ℝ := ∑ b ∈ Finset.range l, D.Wplus x b with hCdef
  have hC0 : 0 < C := by
    refine Finset.sum_pos (fun b _ => D.Wplus_pos hx0 b) ⟨0, Finset.mem_range.2 hl⟩
  have hCb : ∀ b, b < l → D.Wplus x b ≤ C := by
    intro b hb
    refine Finset.single_le_sum (f := fun b => D.Wplus x b)
      (fun i _ => (D.Wplus_pos hx0 i).le) (Finset.mem_range.2 hb)
  have hPpm : ∀ m : ℕ, D.Wplus x m ≤ C * Pp ^ m := by
    intro m
    obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < l ∧ m = a * l + b :=
      ⟨m / l, m % l, Nat.mod_lt _ hl, (Nat.div_add_mod' m l).symm⟩
    have h1 := D.Wplus_mul_add_le x hx0 hx1 l b a
    have hWpow : D.Wplus x l ^ a = Pp ^ (a * l) := by
      rw [hPpdef, ← Real.exp_nat_mul, ← Real.exp_log (D.Wplus_pos hx0 l), ← Real.exp_nat_mul,
        Real.log_exp]
      congr 1
      push_cast
      field_simp
    have hmono : Pp ^ (a * l) ≤ Pp ^ (a * l + b) := pow_le_pow_right₀ hPp1 (Nat.le_add_right _ _)
    calc D.Wplus x (a * l + b) ≤ D.Wplus x l ^ a * D.Wplus x b := h1
      _ = Pp ^ (a * l) * D.Wplus x b := by rw [hWpow]
      _ ≤ Pp ^ (a * l + b) * C := by
          refine mul_le_mul hmono (hCb b hb) (D.Wplus_pos hx0 b).le (by positivity)
      _ = C * Pp ^ (a * l + b) := by ring
  have hPp : ∀ m T : ℕ, ((D.sumSet m T).card : ℝ) * x ^ T ≤ C * Pp ^ m := by
    intro m T
    exact le_trans (D.sumSet_card_mul_pow_le_Wplus x hx0 hx1 m T) (hPpm m)
  have := D.controlled_block_bound_gen x hx0 hx1 k hk Pp C hPp0 hC0 hPp
  rwa [hPplog] at this

/-- The form of equation (25) with `Z_k(x) - 1`, used in the passage to the limit in the
proof of Proposition 5 (`prop:two-pressure`) of `masked_digit_bound.tex`. -/
theorem two_block_bound_sub_one (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (k l : ℕ) (hk : 0 < k)
    (hl : 0 < l) :
    1 + (Real.log (D.Zminus x k - 1) / k - Real.log (D.Wplus x l) / l) / Real.log D.q ≤ C3a := by
  have hfull := D.two_block_bound x hx0 hx1 k l hk hl
  have hZpos : 0 < D.Zminus x k - 1 := by
    have := D.one_lt_Zminus hx0 hx1 hk
    linarith
  have hlog : Real.log (D.Zminus x k - 1) ≤ Real.log (D.Zminus x k) :=
    Real.log_le_log hZpos (by linarith)
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hlogq : 0 < Real.log D.q := Real.log_pos (by exact_mod_cast hq1)
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hstep : (Real.log (D.Zminus x k - 1) / k - Real.log (D.Wplus x l) / l) / Real.log D.q
      ≤ (Real.log (D.Zminus x k) / k - Real.log (D.Wplus x l) / l) / Real.log D.q := by gcongr
  linarith

/-- **Equation (24) (`eq:ultimate-bound`) of Proposition 5 of `masked_digit_bound.tex`:**
`C₃ₐ ≥ 1 + (𝒫₋(x) - 𝒫₊(x)) / log q`. -/
theorem ultimate_bound (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    1 + (D.PminusPressure x - D.PplusPressure x) / Real.log D.q ≤ C3a := by
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hlogq : 0 < Real.log D.q := Real.log_pos (by exact_mod_cast hq1)
  -- for every block length `l ≥ 1`, the difference pressure is bounded by the `l`-block value
  have hstep : ∀ l : ℕ, 1 ≤ l →
      D.PminusPressure x ≤ Real.log (D.Wplus x l) / l + (C3a - 1) * Real.log D.q := by
    intro l hl
    refine D.PminusPressure_le_of_block_bound_full (fun m hm => ?_)
    have hblock := D.two_block_bound x hx0 hx1 m l hm hl
    have h1 : (Real.log (D.Zminus x m) / (m : ℝ) - Real.log (D.Wplus x l) / l)
        / Real.log D.q ≤ C3a - 1 := by linarith
    rw [div_le_iff₀ hlogq] at h1
    linarith
  have hinf : D.PminusPressure x - (C3a - 1) * Real.log D.q ≤ D.PplusPressure x := by
    refine le_csInf ⟨_, ⟨1, le_refl 1, rfl⟩⟩ ?_
    rintro y ⟨l, hl, rfl⟩
    have := hstep l hl
    linarith
  have hfin : (D.PminusPressure x - D.PplusPressure x) / Real.log D.q ≤ C3a - 1 := by
    rw [div_le_iff₀ hlogq]
    linarith
  linarith

/-- **Equation (26) (`eq:finite-two-pressure-certificate`) of Proposition 5 of
`masked_digit_bound.tex`:** the numerical certificate form of the two-sided bound.  It
follows from `ultimate_bound` and `Real.log_div`; keeping it separate isolates the numerical
checker from the analytic proof. -/
theorem finite_pressure_certificate (x c p : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hc : 0 < c) (hp : 0 < p)
    (hminus : Real.log c ≤ D.PminusPressure x)
    (hplus : D.PplusPressure x ≤ Real.log p) :
    1 + Real.log (c / p) / Real.log D.q ≤ C3a := by
  have hq : (1 : ℝ) < (D.q : ℝ) := by
    have : 1 < D.q := lt_of_le_of_lt D.B_pos D.q_gt_B
    exact_mod_cast this
  have hlogq : 0 < Real.log D.q := Real.log_pos hq
  have hmain := D.ultimate_bound x hx0 hx1
  refine le_trans ?_ hmain
  have hnum : Real.log (c / p) ≤ D.PminusPressure x - D.PplusPressure x := by
    rw [Real.log_div (ne_of_gt hc) (ne_of_gt hp)]
    linarith
  gcongr

end MaskData

end MaskedDigit
