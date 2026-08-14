import RequestProject.AutomatonDiff

/-!
# Carry-state certificates for the sum pressure

This file provides the sum-side counterpart of `RequestProject.AutomatonDiff`: the tool used
in Section 4.3 of `masked_digit_bound.tex` to bound the sum pressure `𝒫₊(x)` from above by a
finite computation.

The directed dynamic program of Section 4.1 of the source computes, for each integer output
`y` of `ℓ` sum digits, the minimum digit cost `c⁺_ℓ(y)` producing it; the state of the
computation is the pair of costs of the two possible internal carries `0` and `1`, normalized
so that the smaller one is `0`.  A *finite sum certificate* is a finite automaton on the
canonical base-`q` digits of the output whose state costs are a *lower* bound for the true
ones (`sound0`, `sound1`), so that `x^{c⁺}` — a decreasing function of the cost — is bounded
above.

The main results are

* `SumCert.Wplus_le`: `W_ℓ(x) ≤ 2 ∑_r x^{cost of the run r}`;
* `SumCert.PplusPressure_le_log`: a Collatz--Wielandt positive vector for the automaton
  certifies `𝒫₊(x) ≤ log p`.
-/

open scoped BigOperators
open Filter Topology

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-- The extended sum-digit cost: `s` itself if `s` is a legal sum digit (`s ∈ S = M + M`) and
`+∞` otherwise.  This is the sum-side analogue of the extended difference cost `w` of
Section 4.2 of `masked_digit_bound.tex`. -/
noncomputable def scost (v : ℤ) : ℕ∞ :=
  if 0 ≤ v ∧ v.toNat ∈ D.sumSupport then (v.toNat : ℕ∞) else ⊤

/-- A legal sum digit has finite cost, equal to its value. -/
theorem scost_of_mem {s : ℕ} (hs : s ∈ D.sumSupport) : D.scost (s : ℤ) = (s : ℕ∞) := by
  simp [scost, hs]

/-- **A finite carry certificate for the sum side** (Sections 4.1 and 4.3 of
`masked_digit_bound.tex`).

`u0 s` and `u1 s` are lower bounds for the two costs of the prefix — the cost of producing
the digits read so far with outgoing carry `0` resp. `1` — normalized; reading the canonical
output digit `r` the automaton pays `cost s r` and moves to `next s r`.  The soundness
conditions are the dynamic-programming recursion of Section 4.1, relaxed to the inequality
needed for an upper bound, so that state truncation is allowed. -/
structure SumCert where
  /-- Number of states. -/
  n : ℕ
  /-- Lower bound for the cost of the prefix with outgoing carry `0`, normalized. -/
  u0 : Fin n → ℕ∞
  /-- Lower bound for the cost of the prefix with outgoing carry `1`, normalized. -/
  u1 : Fin n → ℕ∞
  /-- The transition function on canonical output digits. -/
  next : Fin n → ℕ → Fin n
  /-- The cost increment paid on reading an output digit. -/
  cost : Fin n → ℕ → ℕ∞
  /-- The initial state, corresponding to the empty prefix. -/
  start : Fin n
  /-- The empty prefix has cost `0` and outgoing carry `0`. -/
  u0_start : u0 start = 0
  /-- Relaxed form of the dynamic-programming recursion for outgoing carry `0`. -/
  sound0 : ∀ (s : Fin n) (r : ℕ), r < D.q →
    cost s r + u0 (next s r) ≤ min (u0 s + D.scost (r : ℤ)) (u1 s + D.scost ((r : ℤ) - 1))
  /-- Relaxed form of the dynamic-programming recursion for outgoing carry `1`. -/
  sound1 : ∀ (s : Fin n) (r : ℕ), r < D.q →
    cost s r + u1 (next s r)
      ≤ min (u0 s + D.scost ((r : ℤ) + (D.q : ℤ))) (u1 s + D.scost ((r : ℤ) + (D.q : ℤ) - 1))

namespace SumCert

variable {D}

/-- The state reached from `s` after reading the canonical output digits `r`. -/
def runS (A : D.SumCert) : (k : ℕ) → Fin A.n → (Fin k → Fin D.q) → Fin A.n
  | 0, s, _ => s
  | k + 1, s, r => runS A k (A.next s (r 0)) (Fin.tail r)

/-- The total cost paid from `s` while reading the canonical output digits `r`. -/
def runC (A : D.SumCert) : (k : ℕ) → Fin A.n → (Fin k → Fin D.q) → ℕ∞
  | 0, _, _ => 0
  | k + 1, s, r => A.cost s (r 0) + runC A k (A.next s (r 0)) (Fin.tail r)

variable (A : D.SumCert)

theorem runS_succ (k : ℕ) (s : Fin A.n) (r : Fin (k + 1) → Fin D.q) :
    A.runS (k + 1) s r = A.runS k (A.next s (r 0)) (Fin.tail r) := rfl

theorem runC_succ (k : ℕ) (s : Fin A.n) (r : Fin (k + 1) → Fin D.q) :
    A.runC (k + 1) s r = A.cost s (r 0) + A.runC k (A.next s (r 0)) (Fin.tail r) := rfl

/-- Selector for the two costs attached to a state. -/
def uu (A : D.SumCert) : Bool → Fin A.n → ℕ∞
  | false => A.u0
  | true => A.u1

@[simp] theorem uu_false (A : D.SumCert) : A.uu false = A.u0 := rfl
@[simp] theorem uu_true (A : D.SumCert) : A.uu true = A.u1 := rfl

/-- The carry attached to a Boolean, as a natural number. -/
def bn : Bool → ℕ
  | false => 0
  | true => 1

@[simp] theorem bn_false : bn false = 0 := rfl
@[simp] theorem bn_true : bn true = 1 := rfl

/-- The two soundness conditions of a sum certificate, in uniform notation: `b` is the
incoming carry and `c` the outgoing one. -/
theorem sound (A : D.SumCert) (s : Fin A.n) (r : ℕ) (hr : r < D.q) (b c : Bool) :
    A.cost s r + A.uu c (A.next s r)
      ≤ A.uu b s + D.scost ((r : ℤ) + (D.q : ℤ) * (bn c : ℤ) - (bn b : ℤ)) := by
  cases c with
  | false =>
    have h := A.sound0 s r hr
    cases b with
    | false => simpa using le_trans h (min_le_left _ _)
    | true => simpa using le_trans h (min_le_right _ _)
  | true =>
    have h := A.sound1 s r hr
    cases b with
    | false =>
      have : ((r : ℤ) + (D.q : ℤ) * 1 - 0) = (r : ℤ) + (D.q : ℤ) := by ring
      simpa [this] using le_trans h (min_le_left _ _)
    | true =>
      have : ((r : ℤ) + (D.q : ℤ) * 1 - 1) = (r : ℤ) + (D.q : ℤ) - 1 := by ring
      simpa [this] using le_trans h (min_le_right _ _)

/-! ### Every sum word is dominated by a run -/

/-- Value of a sum word obtained by prepending a digit. -/
theorem swValue_cons {k : ℕ} (d : {s : ℕ // s ∈ D.sumSupport}) (w : D.SumWord k) :
    D.swValue (Fin.cons d w) = (d : ℕ) + D.q * D.swValue w := by
  simp only [MaskData.swValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Cost of a sum word obtained by prepending a digit. -/
theorem swCost_cons {k : ℕ} (d : {s : ℕ // s ∈ D.sumSupport}) (w : D.SumWord k) :
    D.swCost (Fin.cons d w) = (d : ℕ) + D.swCost w := by
  simp [MaskData.swCost, Fin.sum_univ_succ]

/-- **The domination invariant.**  Every sum word, read together with an incoming carry, is
dominated by a run of the automaton on the canonical base-`q` digits of the resulting output:
the run is no more expensive than the word.  This is the direction of the path expansion of
Section 4.1 of `masked_digit_bound.tex` needed for the upper bound. -/
theorem exists_run (A : D.SumCert) :
    ∀ (k : ℕ) (s : Fin A.n) (w : D.SumWord k) (b : Bool),
      ∃ (r : Fin k → Fin D.q) (c : Bool),
        (D.swValue w : ℤ) + (bn b : ℤ)
            = (DiffCert.canon (D := D) k r : ℤ) + (bn c : ℤ) * (D.q : ℤ) ^ k ∧
          A.runC k s r + A.uu c (A.runS k s r) ≤ (D.swCost w : ℕ∞) + A.uu b s := by
  intro k
  induction k with
  | zero =>
      intro s w b
      refine ⟨(fun i => absurd i.isLt (by omega)), b, ?_, ?_⟩
      · simp [MaskData.swValue, DiffCert.canon]
      · simp [MaskData.swCost, runC, runS]
  | succ k ih =>
      intro s w b
      have hq : 0 < D.q := lt_of_le_of_lt (Nat.zero_le _) (lt_of_le_of_lt D.B_pos D.q_gt_B)
      set w0 : ℕ := (w 0 : ℕ) with hw0
      have hw0mem : w0 ∈ D.sumSupport := (w 0).2
      have hw0le : w0 ≤ 2 * D.B := D.le_of_mem_sumSupport hw0mem
      have hBq : D.B < D.q := D.q_gt_B
      set t : ℕ := w0 + bn b with ht
      have htlt : t < 2 * D.q := by
        have : bn b ≤ 1 := by cases b <;> simp
        omega
      -- split off the first output digit and the outgoing carry
      set c1 : Bool := decide (D.q ≤ t) with hc1
      set r0 : ℕ := t - D.q * bn c1 with hr0
      have hsplit : t = r0 + D.q * bn c1 := by
        by_cases h : D.q ≤ t
        · simp only [hc1, h, decide_true, bn_true, hr0]
          omega
        · simp only [hc1, h, decide_false, bn_false, hr0]
          omega
      have hr0lt : r0 < D.q := by
        by_cases h : D.q ≤ t
        · simp only [hc1, h, decide_true, bn_true, hr0]
          omega
        · simp only [hc1, h, decide_false, bn_false, hr0]
          omega
      set s' : Fin A.n := A.next s r0 with hs'
      obtain ⟨r', c, hval', hcost'⟩ := ih s' (Fin.tail w) c1
      refine ⟨Fin.cons ⟨r0, hr0lt⟩ r', c, ?_, ?_⟩
      · have hwc : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
        have hcanon : DiffCert.canon (D := D) (k + 1) (Fin.cons ⟨r0, hr0lt⟩ r')
            = r0 + D.q * DiffCert.canon (D := D) k r' := by
          simp [DiffCert.canon]
        have hA : ((w 0 : ℕ) : ℤ) + (bn b : ℤ) = (r0 : ℤ) + (D.q : ℤ) * (bn c1 : ℤ) := by
          have h1 : (t : ℤ) = (r0 : ℤ) + (D.q : ℤ) * (bn c1 : ℤ) := by exact_mod_cast hsplit
          have h2 : ((w 0 : ℕ) : ℤ) + (bn b : ℤ) = (t : ℤ) := by
            simp only [ht, hw0]; push_cast; ring
          linarith
        rw [hwc, swValue_cons, hcanon]
        push_cast
        push_cast at hA hval'
        linear_combination hA + (D.q : ℤ) * hval'
      · have hsnd := A.sound s r0 hr0lt b c1
        have hscost : D.scost ((r0 : ℤ) + (D.q : ℤ) * (bn c1 : ℤ) - (bn b : ℤ))
            = (w0 : ℕ∞) := by
          have harg : (r0 : ℤ) + (D.q : ℤ) * (bn c1 : ℤ) - (bn b : ℤ) = (w0 : ℤ) := by
            have : (t : ℤ) = (r0 : ℤ) + (D.q : ℤ) * (bn c1 : ℤ) := by exact_mod_cast hsplit
            have h2 : (t : ℤ) = (w0 : ℤ) + (bn b : ℤ) := by simp only [ht]; push_cast; ring
            linarith
          rw [harg, D.scost_of_mem hw0mem]
        have hstep : A.cost s r0 + A.uu c1 s' ≤ (w0 : ℕ∞) + A.uu b s := by
          rw [← hscost]
          exact le_trans hsnd (le_of_eq (add_comm _ _))
        have hwc : w = Fin.cons (w 0) (Fin.tail w) := (Fin.cons_self_tail w).symm
        have hcostw : (D.swCost w : ℕ∞) = (w0 : ℕ∞) + (D.swCost (Fin.tail w) : ℕ∞) := by
          rw [hwc, swCost_cons]
          push_cast
          rw [← hwc]
        have hrunC : A.runC (k + 1) s (Fin.cons ⟨r0, hr0lt⟩ r')
            = A.cost s r0 + A.runC k s' r' := by
          rw [A.runC_succ]
          simp [hs']
        have hrunS : A.runS (k + 1) s (Fin.cons ⟨r0, hr0lt⟩ r') = A.runS k s' r' := by
          rw [A.runS_succ]
          simp [hs']
        rw [hrunC, hrunS, hcostw]
        calc A.cost s r0 + A.runC k s' r' + A.uu c (A.runS k s' r')
            = A.cost s r0 + (A.runC k s' r' + A.uu c (A.runS k s' r')) := by ring
          _ ≤ A.cost s r0 + ((D.swCost (Fin.tail w) : ℕ∞) + A.uu c1 s') :=
              add_le_add le_rfl hcost'
          _ = (A.cost s r0 + A.uu c1 s') + (D.swCost (Fin.tail w) : ℕ∞) := by ring
          _ ≤ ((w0 : ℕ∞) + A.uu b s) + (D.swCost (Fin.tail w) : ℕ∞) :=
              add_le_add hstep le_rfl
          _ = (w0 : ℕ∞) + (D.swCost (Fin.tail w) : ℕ∞) + A.uu b s := by ring

/-! ### From runs to `W_ℓ(x)` -/

/-- **`W_ℓ(x)` is at most twice the total weight of all runs of length `ℓ`.**  The factor `2`
is the two possible top carries, as in Section 4.1 of `masked_digit_bound.tex`. -/
theorem Wplus_le (A : D.SumCert) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (l : ℕ) :
    D.Wplus x l ≤ 2 * ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r) := by
  classical
  -- for every attained output, a run of at most the same cost reading its canonical digits
  have hq : 0 < D.q := lt_of_le_of_lt (Nat.zero_le _) (lt_of_le_of_lt D.B_pos D.q_gt_B)
  have hkey : ∀ y : ℕ, ∃ p : (Fin l → Fin D.q) × Bool, y ∈ D.sumOutputs l →
      ((y : ℤ) = (DiffCert.canon (D := D) l p.1 : ℤ) + (bn p.2 : ℤ) * (D.q : ℤ) ^ l ∧
        x ^ D.cPlus l y ≤ epow x (A.runC l A.start p.1)) := by
    intro y
    by_cases hy : y ∈ D.sumOutputs l
    · obtain ⟨w, hwval, hwcost⟩ := D.exists_swCost_eq_cPlus hy
      obtain ⟨r, c, hval, hcost⟩ := A.exists_run l A.start w false
      refine ⟨⟨r, c⟩, fun _ => ⟨?_, ?_⟩⟩
      · simpa [hwval] using hval
      · have hcost2 : A.runC l A.start r ≤ (D.swCost w : ℕ∞) := by
          have h0 : A.runC l A.start r ≤ A.runC l A.start r + A.uu c (A.runS l A.start r) :=
            le_self_add
          have h1 : A.runC l A.start r + A.uu c (A.runS l A.start r)
              ≤ (D.swCost w : ℕ∞) + A.uu false A.start := hcost
          have h2 : A.uu false A.start = 0 := A.u0_start
          rw [h2, add_zero] at h1
          exact le_trans h0 h1
        have hfin : A.runC l A.start r ≠ ⊤ := by
          intro h
          rw [h, top_le_iff] at hcost2
          exact (by simp : ((D.swCost w : ℕ∞)) ≠ ⊤) hcost2
        have hnat : (A.runC l A.start r).toNat ≤ D.swCost w := by
          have hco : ((A.runC l A.start r).toNat : ℕ∞) = A.runC l A.start r := ENat.coe_toNat hfin
          rw [← hco] at hcost2
          exact_mod_cast hcost2
        rw [epow, if_neg hfin, ← hwcost]
        exact pow_le_pow_of_le_one hx0.le hx1 hnat
    · exact ⟨⟨fun _ => ⟨0, hq⟩, false⟩, fun h => absurd h hy⟩
  choose g hg using hkey
  have hinj : Set.InjOn g (D.sumOutputs l : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hg a ha).1
    have h2 := (hg b hb).1
    rw [hab] at h1
    have : (a : ℤ) = (b : ℤ) := by rw [h1, h2]
    exact_mod_cast this
  have hstep1 : D.Wplus x l ≤ ∑ y ∈ D.sumOutputs l, epow x (A.runC l A.start (g y).1) :=
    Finset.sum_le_sum fun y hy => (hg y hy).2
  have hstep2 : ∑ y ∈ D.sumOutputs l, epow x (A.runC l A.start (g y).1)
      = ∑ p ∈ (D.sumOutputs l).image g, epow x (A.runC l A.start p.1) :=
    (Finset.sum_image (g := g) (f := fun p : (Fin l → Fin D.q) × Bool =>
      epow x (A.runC l A.start p.1)) (fun a ha b hb hab => hinj ha hb hab)).symm
  have hstep3 : ∑ p ∈ (D.sumOutputs l).image g, epow x (A.runC l A.start p.1)
      ≤ ∑ p : (Fin l → Fin D.q) × Bool, epow x (A.runC l A.start p.1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => epow_nonneg hx0.le _)
  have hstep4 : ∑ p : (Fin l → Fin D.q) × Bool, epow x (A.runC l A.start p.1)
      = 2 * ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r) := by
    rw [Fintype.sum_prod_type]
    simp [Finset.mul_sum, two_mul]
  calc D.Wplus x l ≤ ∑ y ∈ D.sumOutputs l, epow x (A.runC l A.start (g y).1) := hstep1
    _ = ∑ p ∈ (D.sumOutputs l).image g, epow x (A.runC l A.start p.1) := hstep2
    _ ≤ ∑ p : (Fin l → Fin D.q) × Bool, epow x (A.runC l A.start p.1) := hstep3
    _ = 2 * ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r) := hstep4

/-! ### The Collatz--Wielandt bound -/

/-- **Iterated Collatz--Wielandt inequality for the sum automaton**: a positive vector `V`
with `∑_r x^{cost} V(next) ≤ p · V s` propagates to runs of any length. -/
theorem cw_pow (A : D.SumCert) {x : ℝ} (hx0 : 0 < x) (V : Fin A.n → ℝ) (p : ℝ) (hp : 0 ≤ p)
    (hcw : ∀ s : Fin A.n, ∑ r : Fin D.q, epow x (A.cost s r) * V (A.next s r) ≤ p * V s) :
    ∀ (k : ℕ) (s : Fin A.n),
      ∑ r : Fin k → Fin D.q, epow x (A.runC k s r) * V (A.runS k s r) ≤ p ^ k * V s := by
  intro k
  induction k with
  | zero => intro s; simp [runC, runS]
  | succ k ih =>
      intro s
      have hstep : ∀ r0 : Fin D.q,
          ∑ r' : Fin k → Fin D.q,
              epow x (A.runC (k + 1) s (Fin.cons r0 r')) * V (A.runS (k + 1) s (Fin.cons r0 r'))
            ≤ p ^ k * (epow x (A.cost s r0) * V (A.next s r0)) := by
        intro r0
        have hrw : ∀ r' : Fin k → Fin D.q,
            epow x (A.runC (k + 1) s (Fin.cons r0 r')) * V (A.runS (k + 1) s (Fin.cons r0 r'))
              = epow x (A.cost s r0) * (epow x (A.runC k (A.next s r0) r') *
                  V (A.runS k (A.next s r0) r')) := by
          intro r'
          rw [A.runC_succ, A.runS_succ]
          simp only [Fin.cons_zero, Fin.tail_cons]
          rw [epow_add]
          ring
        rw [Finset.sum_congr rfl (fun r' _ => hrw r'), ← Finset.mul_sum]
        have hle := ih (A.next s r0)
        have hpow : 0 ≤ epow x (A.cost s r0) := epow_nonneg hx0.le _
        calc epow x (A.cost s r0) *
              (∑ r' : Fin k → Fin D.q, epow x (A.runC k (A.next s r0) r') *
                V (A.runS k (A.next s r0) r'))
            ≤ epow x (A.cost s r0) * (p ^ k * V (A.next s r0)) :=
              mul_le_mul_of_nonneg_left hle hpow
          _ = p ^ k * (epow x (A.cost s r0) * V (A.next s r0)) := by ring
      calc ∑ r : Fin (k + 1) → Fin D.q, epow x (A.runC (k + 1) s r) * V (A.runS (k + 1) s r)
          = ∑ r0 : Fin D.q, ∑ r' : Fin k → Fin D.q,
              epow x (A.runC (k + 1) s (Fin.cons r0 r')) *
                V (A.runS (k + 1) s (Fin.cons r0 r')) :=
            DiffCert.sum_succ_split (D := D) k
              (fun r => epow x (A.runC (k + 1) s r) * V (A.runS (k + 1) s r))
        _ ≤ ∑ r0 : Fin D.q, p ^ k * (epow x (A.cost s r0) * V (A.next s r0)) :=
            Finset.sum_le_sum fun r0 _ => hstep r0
        _ = p ^ k * ∑ r0 : Fin D.q, epow x (A.cost s r0) * V (A.next s r0) := by
            rw [Finset.mul_sum]
        _ ≤ p ^ k * (p * V s) := mul_le_mul_of_nonneg_left (hcw s) (pow_nonneg hp k)
        _ = p ^ (k + 1) * V s := by ring

/-- **The finite carry certificate bounds the sum pressure from above.**

This is the sum-side half of the certificate of Section 4.3 of `masked_digit_bound.tex`: a
positive Collatz--Wielandt vector `V` with ratio `p` for the automaton `A` certifies
`𝒫₊(x) ≤ log p`. -/
theorem PplusPressure_le_log (A : D.SumCert) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (V : Fin A.n → ℝ) (p : ℝ) (hp : 0 < p) (hV : ∀ s, 0 < V s)
    (hcw : ∀ s : Fin A.n, ∑ r : Fin D.q, epow x (A.cost s r) * V (A.next s r) ≤ p * V s) :
    D.PplusPressure x ≤ Real.log p := by
  classical
  have hne : Nonempty (Fin A.n) := ⟨A.start⟩
  set Vmin : ℝ := Finset.univ.inf' Finset.univ_nonempty V with hVmin
  have hVmin_le : ∀ s, Vmin ≤ V s := fun s => Finset.inf'_le V (Finset.mem_univ s)
  have hVmin0 : 0 < Vmin := (Finset.lt_inf'_iff _).2 (fun s _ => hV s)
  set K : ℝ := 2 * V A.start / Vmin with hK
  have hK0 : 0 < K := by
    apply div_pos _ hVmin0
    linarith [hV A.start]
  have hW : ∀ l : ℕ, D.Wplus x l ≤ K * p ^ l := by
    intro l
    have h1 := A.cw_pow hx0 V p hp.le hcw l A.start
    have h2 : Vmin * ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r)
        ≤ ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r) * V (A.runS l A.start r) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      have h := epow_nonneg hx0.le (A.runC l A.start r)
      nlinarith [hVmin_le (A.runS l A.start r)]
    have h3 := A.Wplus_le hx0 hx1.le l
    have h4 : Vmin * ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r) ≤ p ^ l * V A.start :=
      le_trans h2 h1
    have h5 : ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r) ≤ p ^ l * V A.start / Vmin := by
      rw [le_div_iff₀ hVmin0]
      nlinarith [h4]
    have h6 : (2 : ℝ) * ∑ r : Fin l → Fin D.q, epow x (A.runC l A.start r)
        ≤ 2 * (p ^ l * V A.start / Vmin) := by linarith
    refine le_trans h3 (le_trans h6 (le_of_eq ?_))
    rw [hK]
    field_simp
  have hlog : ∀ l : ℕ, 1 ≤ l → D.PplusPressure x ≤ Real.log p + Real.log K / l := by
    intro l hl
    have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
    have hWpos : 0 < D.Wplus x l := by
      refine Finset.sum_pos (fun y _ => pow_pos hx0 _) (D.sumOutputs_nonempty l)
    have h1 : Real.log (D.Wplus x l) ≤ Real.log (K * p ^ l) :=
      Real.log_le_log hWpos (hW l)
    rw [Real.log_mul (ne_of_gt hK0) (by positivity), Real.log_pow] at h1
    have h2 := D.PplusPressure_le hx0 hl
    have h3 : Real.log (D.Wplus x l) / l ≤ Real.log p + Real.log K / l := by
      rw [div_le_iff₀ hlR]
      have hexp : (Real.log p + Real.log K / l) * l = Real.log p * l + Real.log K := by
        field_simp
      rw [hexp]
      linarith
    exact le_trans h2 h3
  have hlim : Filter.Tendsto (fun l : ℕ => Real.log p + Real.log K / l) Filter.atTop
      (nhds (Real.log p)) := by
    have : Filter.Tendsto (fun l : ℕ => Real.log K / l) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using this.const_add (Real.log p)
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with l hl
  exact hlog l hl

end SumCert

end MaskData

end MaskedDigit
