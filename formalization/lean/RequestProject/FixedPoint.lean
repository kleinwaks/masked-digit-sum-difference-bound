import Mathlib

/-!
# Certified fixed-point bounds for geometric sums

Section 3 of `masked_digit_bound.tex` evaluates the two partition polynomials

`P₊(x) = ∑_{s ∈ S} xˢ`  and  `P₋(x) = ∑_{d ∈ D} x^{κ(d)}`

at a single fixed fugacity `x = e^{-λ₀}`, using directed (outward-rounded) `384`-bit MPFR
arithmetic, so that the resulting comparison is a rigorous inequality.

This file provides the corresponding certified arithmetic in Lean.  Powers `x^k` are
approximated by natural numbers scaled by `2^S`, computed by an iterated multiply-and-round
recursion; rounding is *downwards* for a lower bound and *upwards* for an upper bound, so the
computed values enclose the exact powers.  Summing the entries along an explicit list of
exponents yields rigorous rational bounds for sums `∑ x^k`.
-/

namespace MaskedDigit

/-! ## Arrays built by a one-step recursion -/

/-- The array `#[init, f init, f (f init), …]` with `n + 1` entries.  Building the values in
an array (rather than recomputing them) is what makes the certified evaluation of the
partition polynomials feasible. -/
def iterArr (f : ℕ → ℕ) (init : ℕ) (n : ℕ) : Array ℕ :=
  (List.range n).foldl (fun arr j => arr.push (f (arr.getD j 0))) #[init]

theorem iterArr_zero (f : ℕ → ℕ) (init : ℕ) : iterArr f init 0 = #[init] := rfl

theorem iterArr_succ (f : ℕ → ℕ) (init n : ℕ) :
    iterArr f init (n + 1) =
      (iterArr f init n).push (f ((iterArr f init n).getD n 0)) := by
  simp [iterArr, List.range_succ]

theorem iterArr_size (f : ℕ → ℕ) (init : ℕ) : ∀ n, (iterArr f init n).size = n + 1
  | 0 => rfl
  | n + 1 => by rw [iterArr_succ]; simp [iterArr_size f init n]

private theorem push_getD_lt (a : Array ℕ) (x : ℕ) (i : ℕ) (h : i < a.size) :
    (a.push x).getD i 0 = a.getD i 0 := by
  simp only [Array.getD, Array.size_push, dif_pos h, dif_pos (Nat.lt_succ_of_lt h)]
  exact Array.getElem_push_lt _

private theorem push_getD_size (a : Array ℕ) (x : ℕ) (i : ℕ) (h : i = a.size) :
    (a.push x).getD i 0 = x := by
  subst h; simp [Array.getD, Array.size_push]

theorem iterArr_getD_of_le (f : ℕ → ℕ) (init : ℕ) {i n : ℕ} (h : i ≤ n) :
    ∀ m, n ≤ m → (iterArr f init m).getD i 0 = (iterArr f init n).getD i 0 := by
  intro m
  induction m with
  | zero =>
      intro hm
      have : n = 0 := by omega
      subst this; rfl
  | succ k ih =>
      intro hm
      rcases Nat.eq_or_lt_of_le hm with he | hlt
      · rw [← he]
      · have hnk : n ≤ k := by omega
        rw [iterArr_succ, push_getD_lt _ _ _ (by rw [iterArr_size]; omega), ih hnk]

theorem iterArr_getD_zero (f : ℕ → ℕ) (init n : ℕ) : (iterArr f init n).getD 0 0 = init := by
  rw [iterArr_getD_of_le f init (Nat.zero_le _) n (Nat.zero_le _)]
  rfl

theorem iterArr_getD_succ (f : ℕ → ℕ) (init : ℕ) {k n : ℕ} (h : k < n) :
    (iterArr f init n).getD (k + 1) 0 = f ((iterArr f init n).getD k 0) := by
  have h1 : (iterArr f init n).getD (k + 1) 0 = (iterArr f init (k + 1)).getD (k + 1) 0 :=
    iterArr_getD_of_le f init (le_refl _) n h
  have h2 : (iterArr f init n).getD k 0 = (iterArr f init k).getD k 0 :=
    iterArr_getD_of_le f init (le_refl _) n (le_of_lt h)
  rw [h1, h2, iterArr_succ]
  exact push_getD_size _ _ _ (by rw [iterArr_size])

/-! ## A tail-recursive sum -/

/-- `∑_{k ∈ l} f k`, computed by a tail-recursive fold so that it can be evaluated on the
long exponent lists of Section 3 of `masked_digit_bound.tex`. -/
def sumMapFold (l : List ℕ) (f : ℕ → ℕ) : ℕ := l.foldl (fun acc k => acc + f k) 0

private theorem sumMapFold_aux (f : ℕ → ℕ) :
    ∀ (l : List ℕ) (a : ℕ), l.foldl (fun acc k => acc + f k) a = a + (l.map f).sum
  | [], a => by simp
  | b :: t, a => by
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, sumMapFold_aux f t]
      ring

theorem sumMapFold_eq (l : List ℕ) (f : ℕ → ℕ) : sumMapFold l f = (l.map f).sum := by
  simp [sumMapFold, sumMapFold_aux f l 0]

/-! ## Directed fixed-point powers -/

/-- Lower fixed-point approximations of the powers `xᵏ` scaled by `2^S`: each step multiplies
by `xlo` and rounds *down*. -/
def fpArrLo (xlo S n : ℕ) : Array ℕ := iterArr (fun a => a * xlo / 2 ^ S) (2 ^ S) n

/-- Upper fixed-point approximations of the powers `xᵏ` scaled by `2^S`: each step multiplies
by `xhi` and rounds *up*. -/
def fpArrHi (xhi S n : ℕ) : Array ℕ :=
  iterArr (fun a => (a * xhi + 2 ^ S - 1) / 2 ^ S) (2 ^ S) n

/-- Rounding a natural-number quotient upwards. -/
theorem ceil_div_ge (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) / d ≤ (((N + d - 1) / d : ℕ) : ℝ) := by
  have hle : N ≤ ((N + d - 1) / d) * d := by
    have h1 : ((N + d - 1) / d) * d + (N + d - 1) % d = N + d - 1 := by
      rw [mul_comm]; exact Nat.div_add_mod _ _
    have h2 := Nat.mod_lt (N + d - 1) hd
    omega
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast hle

/-- **Soundness of the downward-rounded powers**: the entries of `fpArrLo` are at most the
exact powers `xᵏ` scaled by `2^S`. -/
theorem fpArrLo_le (xlo S n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxlo : (xlo : ℝ) ≤ x * 2 ^ S) :
    ∀ k ≤ n, (((fpArrLo xlo S n).getD k 0 : ℕ) : ℝ) ≤ x ^ k * 2 ^ S := by
  intro k
  induction k with
  | zero => intro _; rw [fpArrLo, iterArr_getD_zero]; simp
  | succ j ih =>
      intro hj
      have hjn : j < n := by omega
      rw [fpArrLo, iterArr_getD_succ _ _ hjn]
      set a : ℕ := (iterArr (fun a => a * xlo / 2 ^ S) (2 ^ S) n).getD j 0 with ha
      have hprev : (a : ℝ) ≤ x ^ j * 2 ^ S := ih (by omega)
      have hpow : (0 : ℝ) < 2 ^ S := by positivity
      have hmul : (a : ℝ) * (xlo : ℝ) ≤ (x ^ j * 2 ^ S) * (x * 2 ^ S) :=
        mul_le_mul hprev hxlo (Nat.cast_nonneg _)
          (mul_nonneg (pow_nonneg hx j) (le_of_lt hpow))
      have hfinal : ((a : ℝ) * (xlo : ℝ)) / 2 ^ S ≤ x ^ (j + 1) * 2 ^ S := by
        rw [div_le_iff₀ hpow]
        calc (a : ℝ) * (xlo : ℝ) ≤ (x ^ j * 2 ^ S) * (x * 2 ^ S) := hmul
          _ = x ^ (j + 1) * 2 ^ S * 2 ^ S := by ring
      calc ((a * xlo / 2 ^ S : ℕ) : ℝ) ≤ ((a * xlo : ℕ) : ℝ) / ((2 ^ S : ℕ) : ℝ) :=
            Nat.cast_div_le
        _ = ((a : ℝ) * (xlo : ℝ)) / 2 ^ S := by push_cast; ring
        _ ≤ x ^ (j + 1) * 2 ^ S := hfinal

/-- **Soundness of the upward-rounded powers**: the entries of `fpArrHi` are at least the
exact powers `xᵏ` scaled by `2^S`. -/
theorem fpArrHi_ge (xhi S n : ℕ) (x : ℝ) (hx : 0 ≤ x) (hxhi : x * 2 ^ S ≤ (xhi : ℝ)) :
    ∀ k ≤ n, x ^ k * 2 ^ S ≤ (((fpArrHi xhi S n).getD k 0 : ℕ) : ℝ) := by
  intro k
  induction k with
  | zero => intro _; rw [fpArrHi, iterArr_getD_zero]; simp
  | succ j ih =>
      intro hj
      have hjn : j < n := by omega
      rw [fpArrHi, iterArr_getD_succ _ _ hjn]
      set a : ℕ := (iterArr (fun a => (a * xhi + 2 ^ S - 1) / 2 ^ S) (2 ^ S) n).getD j 0 with ha
      have hprev : x ^ j * 2 ^ S ≤ (a : ℝ) := ih (by omega)
      have hpow : (0 : ℝ) < 2 ^ S := by positivity
      have hmul : (x ^ j * 2 ^ S) * (x * 2 ^ S) ≤ (a : ℝ) * (xhi : ℝ) :=
        mul_le_mul hprev hxhi (mul_nonneg hx (le_of_lt hpow)) (Nat.cast_nonneg _)
      have hstep : x ^ (j + 1) * 2 ^ S ≤ ((a : ℝ) * (xhi : ℝ)) / 2 ^ S := by
        rw [le_div_iff₀ hpow]
        calc x ^ (j + 1) * 2 ^ S * 2 ^ S = (x ^ j * 2 ^ S) * (x * 2 ^ S) := by ring
          _ ≤ (a : ℝ) * (xhi : ℝ) := hmul
      refine le_trans hstep ?_
      have hc := ceil_div_ge (a * xhi) (2 ^ S) (by positivity)
      have hcast : ((a : ℝ) * (xhi : ℝ)) / 2 ^ S = ((a * xhi : ℕ) : ℝ) / ((2 ^ S : ℕ) : ℝ) := by
        push_cast; ring
      rw [hcast]
      exact hc

/-! ## Bounds for sums of powers along a list of exponents -/

/-- A rigorous lower bound for `∑_{k ∈ l} xᵏ`, computed in fixed point. -/
theorem sum_pow_ge (l : List ℕ) (xlo S n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hxlo : (xlo : ℝ) ≤ x * 2 ^ S) (hl : ∀ k ∈ l, k ≤ n) :
    (((l.map fun k => (fpArrLo xlo S n).getD k 0).sum : ℕ) : ℝ) ≤
      (l.map fun k => x ^ k).sum * 2 ^ S := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hmem : ∀ k ∈ t, k ≤ n := fun k hk => hl k (List.mem_cons_of_mem _ hk)
      have ha : a ≤ n := hl a (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have h1 := fpArrLo_le xlo S n x hx hxlo a ha
      have h2 := ih hmem
      calc (((fpArrLo xlo S n).getD a 0 : ℕ) : ℝ) +
            (((t.map fun k => (fpArrLo xlo S n).getD k 0).sum : ℕ) : ℝ)
          ≤ x ^ a * 2 ^ S + (t.map fun k => x ^ k).sum * 2 ^ S := by linarith
        _ = (x ^ a + (t.map fun k => x ^ k).sum) * 2 ^ S := by ring

/-- A rigorous upper bound for `∑_{k ∈ l} xᵏ`, computed in fixed point. -/
theorem sum_pow_le (l : List ℕ) (xhi S n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hxhi : x * 2 ^ S ≤ (xhi : ℝ)) (hl : ∀ k ∈ l, k ≤ n) :
    (l.map fun k => x ^ k).sum * 2 ^ S ≤
      (((l.map fun k => (fpArrHi xhi S n).getD k 0).sum : ℕ) : ℝ) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have hmem : ∀ k ∈ t, k ≤ n := fun k hk => hl k (List.mem_cons_of_mem _ hk)
      have ha : a ≤ n := hl a (List.mem_cons_self ..)
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have h1 := fpArrHi_ge xhi S n x hx hxhi a ha
      have h2 := ih hmem
      calc (x ^ a + (t.map fun k => x ^ k).sum) * 2 ^ S
          = x ^ a * 2 ^ S + (t.map fun k => x ^ k).sum * 2 ^ S := by ring
        _ ≤ (((fpArrHi xhi S n).getD a 0 : ℕ) : ℝ) +
              (((t.map fun k => (fpArrHi xhi S n).getD k 0).sum : ℕ) : ℝ) := by linarith

end MaskedDigit
