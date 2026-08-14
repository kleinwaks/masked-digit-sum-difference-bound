import RequestProject.CarryStates

/-!
# Carry-state certificates for the difference pressure

This file provides the tool used in Section 4.3 of `masked_digit_bound.tex` to bound the
difference pressure `𝒫₋(x)` from below by a finite computation: a *finite carry certificate*,
i.e. a finite deterministic automaton reading the canonical base-`q` digits of a residue and
computing (an upper bound for) the minimum cost `c_k(r)` of equation (16)
(`eq:controlled-cost`) of the source.

This is the difference-side content of Section 4.2 ("The carry-state transfer operator") and
of Proposition 6 (`prop:controlled-finite-graph`) of `masked_digit_bound.tex`, in the form in
which it is actually used: the state of the automaton records the pair of costs
`(C^{(0)}, C^{(1)})` of the two representatives of a canonical prefix residue, normalized so
that the smaller one is `0`, and the source's transition rule (29) (`eq:carry-transition`) is
imposed only as an *inequality* (`sound0`, `sound1`), so that any finite over-approximation of
the exact state graph — in particular the truncation to `|δ| ≤ Δ` used in the verified
certificate — is admissible.

The main results are

* `DiffCert.runSum_le_Zminus`: the total weight of all length-`k` runs is at most `Z_k(x)`;
* `DiffCert.log_le_PminusPressure`: a Collatz–Wielandt positive vector for the automaton,
  as in equation (32) (`eq:controlled-collatz`) of the source, certifies
  `log c ≤ 𝒫₋(x)`.
-/

open scoped BigOperators
open Filter Topology

namespace MaskedDigit

/-- `x ^ c` for an extended natural `c`, with the convention `x ^ ∞ = 0` used throughout
Section 4.2 of `masked_digit_bound.tex`. -/
noncomputable def epow (x : ℝ) (c : ℕ∞) : ℝ := if c = ⊤ then 0 else x ^ c.toNat

@[simp] theorem epow_top (x : ℝ) : epow x ⊤ = 0 := by simp [epow]

@[simp] theorem epow_coe (x : ℝ) (n : ℕ) : epow x (n : ℕ∞) = x ^ n := by
  simp [epow]

@[simp] theorem epow_zero (x : ℝ) : epow x 0 = 1 := by
  have : ((0 : ℕ) : ℕ∞) = 0 := rfl
  rw [← this, epow_coe]; simp

theorem epow_nonneg {x : ℝ} (hx : 0 ≤ x) (c : ℕ∞) : 0 ≤ epow x c := by
  unfold epow
  split
  · exact le_refl 0
  · exact pow_nonneg hx _

theorem epow_add {x : ℝ} (a b : ℕ∞) : epow x (a + b) = epow x a * epow x b := by
  cases a with
  | top => simp
  | coe m =>
    cases b with
    | top => simp
    | coe n =>
      have : ((m : ℕ∞) + (n : ℕ∞)) = ((m + n : ℕ) : ℕ∞) := by push_cast; ring
      rw [this, epow_coe, epow_coe, epow_coe, pow_add]

theorem epow_le_epow_of_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) {a b : ℕ∞} (hab : a ≤ b) :
    epow x b ≤ epow x a := by
  cases b with
  | top => simpa using epow_nonneg hx0.le a
  | coe n =>
    cases a with
    | top => exact absurd hab (by simp)
    | coe m =>
      have hmn : m ≤ n := by exact_mod_cast hab
      simpa using pow_le_pow_of_le_one hx0.le hx1 hmn

namespace MaskData

variable (D : MaskData)

/-- **A finite carry certificate for the difference side** (Section 4.2 and Proposition 6 of
`masked_digit_bound.tex`).

`u0 s` and `u1 s` are the two normalized costs `C^{(0)}, C^{(1)}` attached to the state `s`;
reading the canonical digit `r` the automaton pays `cost s r` and moves to `next s r`.  The
two soundness conditions are the transition rule (29) (`eq:carry-transition`) of the source,
relaxed to an inequality so that state truncation is allowed. -/
structure DiffCert where
  /-- Number of states. -/
  n : ℕ
  /-- Cost of the carry-`0` representative of the prefix, normalized. -/
  u0 : Fin n → ℕ∞
  /-- Cost of the carry-`1` representative of the prefix, normalized. -/
  u1 : Fin n → ℕ∞
  /-- The transition function on canonical digits. -/
  next : Fin n → ℕ → Fin n
  /-- The cost increment `a(δ, r)` of Section 4.2 of `masked_digit_bound.tex`. -/
  cost : Fin n → ℕ → ℕ∞
  /-- The initial state, corresponding to the empty prefix. -/
  start : Fin n
  /-- The empty prefix has no carry-`1` representative. -/
  u1_start : u1 start = ⊤
  /-- Relaxed form of the first line of the transition rule (29) of the source. -/
  sound0 : ∀ (s : Fin n) (r : ℕ), r < D.q →
    min (u0 s + D.wcost (r : ℤ)) (u1 s + D.wcost ((r : ℤ) + 1)) ≤ cost s r + u0 (next s r)
  /-- Relaxed form of the second line of the transition rule (29) of the source. -/
  sound1 : ∀ (s : Fin n) (r : ℕ), r < D.q →
    min (u0 s + D.wcost ((r : ℤ) - (D.q : ℤ))) (u1 s + D.wcost ((r : ℤ) + 1 - (D.q : ℤ)))
      ≤ cost s r + u1 (next s r)
  /-- The two costs attached to a state are normalized so that the smaller one is `0`. -/
  norm : ∀ s, u0 s = 0 ∨ u1 s = 0

namespace DiffCert

variable {D}

/-- The state reached from `s` after reading the canonical digits `r`. -/
def runS (A : D.DiffCert) : (k : ℕ) → Fin A.n → (Fin k → Fin D.q) → Fin A.n
  | 0, s, _ => s
  | k + 1, s, r => runS A k (A.next s (r 0)) (Fin.tail r)

/-- The total cost paid from `s` while reading the canonical digits `r`. -/
def runC (A : D.DiffCert) : (k : ℕ) → Fin A.n → (Fin k → Fin D.q) → ℕ∞
  | 0, _, _ => 0
  | k + 1, s, r => A.cost s (r 0) + runC A k (A.next s (r 0)) (Fin.tail r)

variable (A : D.DiffCert)

@[simp] theorem runS_zero (s : Fin A.n) (r : Fin 0 → Fin D.q) : A.runS 0 s r = s := rfl
@[simp] theorem runC_zero (s : Fin A.n) (r : Fin 0 → Fin D.q) : A.runC 0 s r = 0 := rfl

theorem runS_succ (k : ℕ) (s : Fin A.n) (r : Fin (k + 1) → Fin D.q) :
    A.runS (k + 1) s r = A.runS k (A.next s (r 0)) (Fin.tail r) := rfl

theorem runC_succ (k : ℕ) (s : Fin A.n) (r : Fin (k + 1) → Fin D.q) :
    A.runC (k + 1) s r = A.cost s (r 0) + A.runC k (A.next s (r 0)) (Fin.tail r) := rfl

/-- The residue `∑ᵢ rᵢ qⁱ` read by a run. -/
def canon : (k : ℕ) → (Fin k → Fin D.q) → ℕ
  | 0, _ => 0
  | k + 1, r => (r 0 : ℕ) + D.q * canon k (Fin.tail r)

theorem canon_lt : ∀ (k : ℕ) (r : Fin k → Fin D.q), canon (D := D) k r < D.q ^ k
  | 0, _ => by simp [canon]
  | k + 1, r => by
      have h := canon_lt k (Fin.tail r)
      have h0 : (r 0 : ℕ) < D.q := (r 0).isLt
      have key : D.q * canon (D := D) k (Fin.tail r) + D.q ≤ D.q ^ (k + 1) := by
        have h1 : canon (D := D) k (Fin.tail r) + 1 ≤ D.q ^ k := h
        calc D.q * canon (D := D) k (Fin.tail r) + D.q
            = D.q * (canon (D := D) k (Fin.tail r) + 1) := by ring
          _ ≤ D.q * D.q ^ k := Nat.mul_le_mul_left _ h1
          _ = D.q ^ (k + 1) := by ring
      show (r 0 : ℕ) + D.q * canon (D := D) k (Fin.tail r) < D.q ^ (k + 1)
      omega
/-- The residue map is injective on canonical digit strings. -/
theorem canon_injective (k : ℕ) : Function.Injective (canon (D := D) k) := by
  induction k with
  | zero => intro a b _; funext i; exact absurd i.isLt (by omega)
  | succ k ih =>
      intro a b hab
      have hq : 0 < D.q := lt_of_le_of_lt (Nat.zero_le _) (lt_of_le_of_lt D.B_pos D.q_gt_B)
      simp only [canon] at hab
      have h0 : (a 0 : ℕ) = (b 0 : ℕ) := by
        have h := congrArg (fun t => t % D.q) hab
        simp only [Nat.add_mul_mod_self_left] at h
        rwa [Nat.mod_eq_of_lt (a 0).isLt, Nat.mod_eq_of_lt (b 0).isLt] at h
      have h1 : canon (D := D) k (Fin.tail a) = canon (D := D) k (Fin.tail b) := by
        have h2 : D.q * canon (D := D) k (Fin.tail a)
            = D.q * canon (D := D) k (Fin.tail b) := by omega
        exact Nat.eq_of_mul_eq_mul_left hq h2
      have h2 := ih h1
      funext i
      refine Fin.cases ?_ ?_ i
      · exact Fin.ext h0
      · intro j
        have := congrFun h2 j
        simpa [Fin.tail] using this

/-! ### The word realized by a run -/

/-- Selector for the two costs attached to a state. -/
def uu (A : D.DiffCert) : Bool → Fin A.n → ℕ∞
  | false => A.u0
  | true => A.u1

/-- The carry value attached to a Boolean. -/
def bv : Bool → ℤ
  | false => 0
  | true => 1

@[simp] theorem uu_false (A : D.DiffCert) : A.uu false = A.u0 := rfl
@[simp] theorem uu_true (A : D.DiffCert) : A.uu true = A.u1 := rfl
@[simp] theorem bv_false : bv false = 0 := rfl
@[simp] theorem bv_true : bv true = 1 := rfl

/-- The two soundness conditions of a certificate, in uniform notation. -/
theorem sound (A : D.DiffCert) (s : Fin A.n) (r : ℕ) (hr : r < D.q) (j : Bool) :
    min (A.u0 s + D.wcost ((r : ℤ) - (D.q : ℤ) * bv j))
        (A.u1 s + D.wcost ((r : ℤ) + 1 - (D.q : ℤ) * bv j))
      ≤ A.cost s r + A.uu j (A.next s r) := by
  cases j with
  | false => simpa using A.sound0 s r hr
  | true => simpa using A.sound1 s r hr

/-- Value of a signed difference word obtained by prepending a digit. -/
theorem dwValue_cons {k : ℕ} (d : {d : ℤ // d ∈ D.diffSupport}) (v : D.DiffWord k) :
    D.dwValue (Fin.cons d v) = (d : ℤ) + (D.q : ℤ) * D.dwValue v := by
  simp only [MaskData.dwValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Cost of a signed difference word obtained by prepending a digit. -/
theorem dwCost_cons {k : ℕ} (d : {d : ℤ // d ∈ D.diffSupport}) (v : D.DiffWord k) :
    D.dwCost (Fin.cons d v) = D.kappa (d : ℤ) + D.dwCost v := by
  simp [MaskData.dwCost, Fin.sum_univ_succ]

/-- **The realizability invariant.**  Every finite-cost run of the automaton is realized by an
actual signed difference word of at most the same cost, whose value differs from the residue
read by the run only by the carries at the two ends.  This is the content of the path
expansion (28) of `masked_digit_bound.tex`, in the direction needed for the lower bound. -/
theorem exists_word (A : D.DiffCert) :
    ∀ (k : ℕ) (s : Fin A.n) (r : Fin k → Fin D.q) (j : Bool),
      A.uu j (A.runS k s r) ≠ ⊤ → A.runC k s r ≠ ⊤ →
      ∃ (i : Bool) (v : D.DiffWord k),
        A.uu i s ≠ ⊤ ∧
        D.dwValue v = (canon (D := D) k r : ℤ) + bv i - bv j * (D.q : ℤ) ^ k ∧
        (D.dwCost v : ℕ∞) + A.uu i s ≤ A.runC k s r + A.uu j (A.runS k s r) := by
  intro k
  induction k with
  | zero =>
      intro s r j hj _
      refine ⟨j, (fun i => absurd i.isLt (by omega)), hj, ?_, ?_⟩
      · simp [MaskData.dwValue, canon]
      · simp [MaskData.dwCost]
  | succ k ih =>
      intro s r j hj hc
      set r0 : ℕ := (r 0 : ℕ) with hr0
      set s' : Fin A.n := A.next s r0 with hs'
      have hrun : A.runS (k + 1) s r = A.runS k s' (Fin.tail r) := rfl
      have hcost : A.runC (k + 1) s r = A.cost s r0 + A.runC k s' (Fin.tail r) := rfl
      have hc1 : A.cost s r0 ≠ ⊤ := by
        intro h; rw [hcost, h, top_add] at hc; exact hc rfl
      have hc2 : A.runC k s' (Fin.tail r) ≠ ⊤ := by
        intro h; rw [hcost, h, add_top] at hc; exact hc rfl
      obtain ⟨c, v', hc'ne, hval', hcost'⟩ := ih s' (Fin.tail r) j (by rwa [hrun] at hj) hc2
      -- the transition inequality at the first digit
      have hsnd := A.sound s r0 (r 0).isLt c
      have hfin : A.cost s r0 + A.uu c s' ≠ ⊤ := by
        intro h
        rcases WithTop.add_eq_top.1 h with h' | h'
        · exact hc1 h'
        · exact hc'ne h'
      -- pick the cheaper of the two incoming branches
      set t0 : ℕ∞ := A.u0 s + D.wcost ((r0 : ℤ) - (D.q : ℤ) * bv c) with ht0
      set t1 : ℕ∞ := A.u1 s + D.wcost ((r0 : ℤ) + 1 - (D.q : ℤ) * bv c) with ht1
      have hmin : min t0 t1 ≤ A.cost s r0 + A.uu c s' := hsnd
      obtain ⟨i, hi⟩ : ∃ i : Bool,
          A.uu i s + D.wcost ((r0 : ℤ) + bv i - (D.q : ℤ) * bv c) ≤ A.cost s r0 + A.uu c s' := by
        rcases le_total t0 t1 with h | h
        · refine ⟨false, ?_⟩
          have : t0 ≤ A.cost s r0 + A.uu c s' := le_trans (le_min le_rfl h) hmin
          simpa [ht0] using this
        · refine ⟨true, ?_⟩
          have : t1 ≤ A.cost s r0 + A.uu c s' := le_trans (le_min h le_rfl) hmin
          simpa [ht1] using this
      set dd : ℤ := (r0 : ℤ) + bv i - (D.q : ℤ) * bv c with hdd
      have hisum : A.uu i s + D.wcost dd ≠ ⊤ := fun h => hfin (top_le_iff.1 (h ▸ hi))
      have huine : A.uu i s ≠ ⊤ := by
        intro h; rw [h, top_add] at hisum; exact hisum rfl
      have hwne : D.wcost dd ≠ ⊤ := by
        intro h; rw [h, add_top] at hisum; exact hisum rfl
      have hddmem : dd ∈ D.diffSupport := by
        by_contra hcon
        rw [MaskData.wcost, if_neg hcon] at hwne
        exact hwne rfl
      have hwval : D.wcost dd = (D.kappa dd : ℕ∞) := by
        rw [MaskData.wcost, if_pos hddmem]
      refine ⟨i, Fin.cons ⟨dd, hddmem⟩ v', huine, ?_, ?_⟩
      · rw [dwValue_cons, hval']
        simp only [canon, hdd]
        push_cast
        ring
      · rw [dwCost_cons]
        have h1 : A.uu i s + (D.kappa dd : ℕ∞) ≤ A.cost s r0 + A.uu c s' := by
          rw [← hwval]; exact hi
        have h2 : (D.dwCost v' : ℕ∞) + A.uu c s'
            ≤ A.runC k s' (Fin.tail r) + A.uu j (A.runS k s' (Fin.tail r)) := hcost'
        have hsum := add_le_add h1 h2
        have hcast : ((D.kappa dd + D.dwCost v' : ℕ) : ℕ∞)
            = (D.kappa dd : ℕ∞) + (D.dwCost v' : ℕ∞) := by push_cast; ring
        rw [hcast, hrun, hcost]
        have hcancel : ∀ a b : ℕ∞, a + A.uu c s' ≤ b + A.uu c s' → a ≤ b := by
          intro a b hab
          exact (WithTop.add_le_add_iff_right hc'ne).1 hab
        refine hcancel _ _ ?_
        calc (D.kappa dd : ℕ∞) + (D.dwCost v' : ℕ∞) + A.uu i s + A.uu c s'
            = (A.uu i s + (D.kappa dd : ℕ∞)) + ((D.dwCost v' : ℕ∞) + A.uu c s') := by ring
          _ ≤ (A.cost s r0 + A.uu c s')
              + (A.runC k s' (Fin.tail r) + A.uu j (A.runS k s' (Fin.tail r))) := hsum
          _ = A.cost s r0 + A.runC k s' (Fin.tail r)
              + A.uu j (A.runS k s' (Fin.tail r)) + A.uu c s' := by ring

/-! ### From runs to the block partition sum -/

/-- The empty prefix has cost `0` in its carry-`0` representative. -/
theorem u0_start (A : D.DiffCert) : A.u0 A.start = 0 := by
  rcases A.norm A.start with h | h
  · exact h
  · rw [A.u1_start] at h; exact absurd h (by simp)

/-- By the normalization condition, every state has a representative of cost `0`. -/
theorem exists_norm_zero (A : D.DiffCert) (s : Fin A.n) : ∃ j : Bool, A.uu j s = 0 := by
  rcases A.norm s with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- **Every finite-cost run realizes an attainable residue**, of block cost at most the cost
of the run.  This is the step of Section 4.2 of `masked_digit_bound.tex` in which a path of
the carry-state graph is converted into a signed difference word. -/
theorem canon_mem_attainable (A : D.DiffCert) (k : ℕ) (r : Fin k → Fin D.q)
    (h : A.runC k A.start r ≠ ⊤) :
    canon (D := D) k r ∈ D.attainableRes k ∧
      D.cMinus k (canon (D := D) k r : ℤ) ≤ (A.runC k A.start r).toNat := by
  obtain ⟨j, hj⟩ := A.exists_norm_zero (A.runS k A.start r)
  have hjne : A.uu j (A.runS k A.start r) ≠ ⊤ := by rw [hj]; simp
  obtain ⟨i, v, hine, hval, hcost⟩ := A.exists_word k A.start r j hjne h
  have hi : i = false := by
    cases i with
    | false => rfl
    | true => exact absurd (show A.uu true A.start = ⊤ from A.u1_start) hine
  subst hi
  have hmod : D.dwValue v ≡ (canon (D := D) k r : ℤ) [ZMOD (D.q : ℤ) ^ k] := by
    refine (Int.modEq_iff_dvd.2 ?_)
    refine ⟨bv j, ?_⟩
    rw [hval]
    simp only [bv_false]
    ring
  have hmem : canon (D := D) k r ∈ D.attainableRes k := by
    simp only [MaskData.attainableRes, Finset.mem_filter, Finset.mem_range]
    exact ⟨canon_lt k r, v, hmod⟩
  refine ⟨hmem, ?_⟩
  have hc1 : D.cMinus k (canon (D := D) k r : ℤ) ≤ D.dwCost v := D.cMinus_le v hmod
  have hc2 : (D.dwCost v : ℕ∞) ≤ A.runC k A.start r := by
    have := hcost
    rw [hj, uu_false, A.u0_start, add_zero, add_zero] at this
    exact this
  have hc3 : D.dwCost v ≤ (A.runC k A.start r).toNat := by
    have hco : ((A.runC k A.start r).toNat : ℕ∞) = A.runC k A.start r :=
      ENat.coe_toNat h
    rw [← hco] at hc2
    exact_mod_cast hc2
  omega

/-- **The total weight of all runs of length `k` is at most `Z_k(x)`.**  Together with the
Collatz--Wielandt bound below this is the finite-certificate lower bound for the difference
pressure used in Section 4.3 of `masked_digit_bound.tex`. -/
theorem runSum_le_Zminus (A : D.DiffCert) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (k : ℕ) :
    ∑ r : Fin k → Fin D.q, epow x (A.runC k A.start r) ≤ D.Zminus x k := by
  classical
  set U : Finset (Fin k → Fin D.q) :=
    Finset.univ.filter (fun r => A.runC k A.start r ≠ ⊤) with hU
  have hsplit : ∑ r : Fin k → Fin D.q, epow x (A.runC k A.start r)
      = ∑ r ∈ U, epow x (A.runC k A.start r) := by
    refine (Finset.sum_subset (Finset.subset_univ U) ?_).symm
    intro r _ hr
    have : A.runC k A.start r = ⊤ := by
      by_contra hcon
      exact hr (by simp [hU, hcon])
    simp [this]
  have hterm : ∀ r ∈ U, epow x (A.runC k A.start r) ≤ x ^ D.cMinus k (canon (D := D) k r : ℤ) := by
    intro r hr
    have hne : A.runC k A.start r ≠ ⊤ := by
      simpa [hU] using hr
    obtain ⟨-, hle⟩ := A.canon_mem_attainable k r hne
    rw [epow, if_neg hne]
    exact pow_le_pow_of_le_one hx0.le hx1 hle
  have hinj : Set.InjOn (canon (D := D) k) U := fun a _ b _ hab => canon_injective k hab
  have hsub : U.image (canon (D := D) k) ⊆ D.attainableRes k := by
    intro n hn
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hn
    have hne : A.runC k A.start r ≠ ⊤ := by simpa [hU] using hr
    exact (A.canon_mem_attainable k r hne).1
  calc ∑ r : Fin k → Fin D.q, epow x (A.runC k A.start r)
      = ∑ r ∈ U, epow x (A.runC k A.start r) := hsplit
    _ ≤ ∑ r ∈ U, x ^ D.cMinus k (canon (D := D) k r : ℤ) := Finset.sum_le_sum hterm
    _ = ∑ n ∈ U.image (canon (D := D) k), x ^ D.cMinus k (n : ℤ) :=
        (Finset.sum_image (g := canon (D := D) k)
          (f := fun n : ℕ => x ^ D.cMinus k (n : ℤ))
          (fun a ha b hb hab => hinj ha hb hab)).symm
    _ ≤ ∑ n ∈ D.attainableRes k, x ^ D.cMinus k (n : ℤ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg hx0.le _)

/-! ### The Collatz--Wielandt bound -/

/-- Splitting a sum over digit strings of length `k + 1` into the first digit and the rest. -/
theorem sum_succ_split {M : Type*} [AddCommMonoid M] (k : ℕ) (f : (Fin (k + 1) → Fin D.q) → M) :
    ∑ r : Fin (k + 1) → Fin D.q, f r
      = ∑ r0 : Fin D.q, ∑ r' : Fin k → Fin D.q, f (Fin.cons r0 r') := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin D.q))
      (fun p => f (Fin.cons p.1 p.2)) f (fun p => rfl)
  rw [← h, Fintype.sum_prod_type]

/-- **Iterated Collatz--Wielandt inequality for the automaton**, the form of equation (32)
(`eq:controlled-collatz`) of `masked_digit_bound.tex` used here: a positive vector `V` with
`c · V s ≤ ∑_r x^{a(s,r)} V(Φ(s,r))` propagates to runs of any length. -/
theorem cw_pow (A : D.DiffCert) {x : ℝ} (hx0 : 0 < x) (V : Fin A.n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcw : ∀ s : Fin A.n, c * V s ≤ ∑ r : Fin D.q, epow x (A.cost s r) * V (A.next s r)) :
    ∀ (k : ℕ) (s : Fin A.n),
      c ^ k * V s ≤ ∑ r : Fin k → Fin D.q, epow x (A.runC k s r) * V (A.runS k s r) := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
      intro s
      have hstep : ∀ r0 : Fin D.q,
          c ^ k * (epow x (A.cost s r0) * V (A.next s r0))
            ≤ ∑ r' : Fin k → Fin D.q,
                epow x (A.runC (k + 1) s (Fin.cons r0 r')) * V (A.runS (k + 1) s (Fin.cons r0 r')) := by
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
        have hge := ih (A.next s r0)
        have hpow : 0 ≤ epow x (A.cost s r0) := epow_nonneg hx0.le _
        calc c ^ k * (epow x (A.cost s r0) * V (A.next s r0))
            = epow x (A.cost s r0) * (c ^ k * V (A.next s r0)) := by ring
          _ ≤ epow x (A.cost s r0) *
              (∑ r' : Fin k → Fin D.q, epow x (A.runC k (A.next s r0) r') *
                V (A.runS k (A.next s r0) r')) := by
              exact mul_le_mul_of_nonneg_left hge hpow
      calc c ^ (k + 1) * V s = c ^ k * (c * V s) := by ring
        _ ≤ c ^ k * ∑ r0 : Fin D.q, epow x (A.cost s r0) * V (A.next s r0) :=
            mul_le_mul_of_nonneg_left (hcw s) (pow_nonneg hc k)
        _ = ∑ r0 : Fin D.q, c ^ k * (epow x (A.cost s r0) * V (A.next s r0)) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ r0 : Fin D.q, ∑ r' : Fin k → Fin D.q,
              epow x (A.runC (k + 1) s (Fin.cons r0 r')) *
                V (A.runS (k + 1) s (Fin.cons r0 r')) := Finset.sum_le_sum fun r0 _ => hstep r0
        _ = ∑ r : Fin (k + 1) → Fin D.q, epow x (A.runC (k + 1) s r) * V (A.runS (k + 1) s r) :=
            (sum_succ_split (D := D) k
              (fun r => epow x (A.runC (k + 1) s r) * V (A.runS (k + 1) s r))).symm

/-- **The finite carry certificate bounds the difference pressure from below.**

This is the difference-side half of the certificate of Section 4.3 of
`masked_digit_bound.tex`: a positive Collatz--Wielandt vector `V` with ratio `c` for the
automaton `A` certifies `log c ≤ 𝒫₋(x)`. -/
theorem log_le_PminusPressure (A : D.DiffCert) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (V : Fin A.n → ℝ) (c : ℝ) (hc : 0 < c) (hV : ∀ s, 0 < V s)
    (hcw : ∀ s : Fin A.n, c * V s ≤ ∑ r : Fin D.q, epow x (A.cost s r) * V (A.next s r)) :
    Real.log c ≤ D.PminusPressure x := by
  classical
  have hne : Nonempty (Fin A.n) := ⟨A.start⟩
  set Vmax : ℝ := Finset.univ.sup' Finset.univ_nonempty V with hVmax
  have hVmax_ge : ∀ s, V s ≤ Vmax := fun s => Finset.le_sup' V (Finset.mem_univ s)
  have hVmax0 : 0 < Vmax := lt_of_lt_of_le (hV A.start) (hVmax_ge A.start)
  set K : ℝ := V A.start / Vmax with hK
  have hK0 : 0 < K := div_pos (hV A.start) hVmax0
  have hZ : ∀ k : ℕ, K * c ^ k ≤ D.Zminus x k := by
    intro k
    have h1 := A.cw_pow hx0 V c hc.le hcw k A.start
    have h2 : ∑ r : Fin k → Fin D.q, epow x (A.runC k A.start r) * V (A.runS k A.start r)
        ≤ Vmax * ∑ r : Fin k → Fin D.q, epow x (A.runC k A.start r) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun r _ => ?_
      have := epow_nonneg hx0.le (A.runC k A.start r)
      nlinarith [hVmax_ge (A.runS k A.start r)]
    have h3 := A.runSum_le_Zminus hx0 hx1.le k
    have h4 : c ^ k * V A.start ≤ Vmax * D.Zminus x k := by
      nlinarith [h1, h2, h3, hVmax0]
    rw [hK, div_mul_eq_mul_div, div_le_iff₀ hVmax0]
    nlinarith [h4]
  have hlog : ∀ k : ℕ, 1 ≤ k → Real.log c + Real.log K / k ≤ D.PminusPressure x := by
    intro k hk
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have h1 : Real.log (K * c ^ k) ≤ Real.log (D.Zminus x k) :=
      Real.log_le_log (by positivity) (hZ k)
    rw [Real.log_mul (ne_of_gt hK0) (by positivity), Real.log_pow] at h1
    have h2 := D.le_PminusPressure hx0 hx1 hk
    rw [div_le_iff₀ hkR] at h2
    have hexp : (Real.log c + Real.log K / k) * k = Real.log c * k + Real.log K := by
      field_simp
    have key : (Real.log c + Real.log K / k) * k ≤ D.PminusPressure x * k := by
      rw [hexp]; linarith
    exact le_of_mul_le_mul_right key hkR
  have hlim : Filter.Tendsto (fun k : ℕ => Real.log c + Real.log K / k) Filter.atTop
      (nhds (Real.log c)) := by
    have : Filter.Tendsto (fun k : ℕ => Real.log K / k) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using this.const_add (Real.log c)
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  exact hlog k hk

end DiffCert

end MaskData

end MaskedDigit
