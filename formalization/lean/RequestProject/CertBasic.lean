import RequestProject.AutomatonSum
import CertKernel.Basic

/-!
# Elementary lemmas for the controlled-carry certificate kernel

This file provides the interface between the integer kernel `CertKernel.Basic` — the
computational part of the verification of the two numerical facts of Section 4.3 of
`masked_digit_bound.tex` — and the mathematics of `RequestProject.AutomatonDiff` and
`RequestProject.AutomatonSum`.

It contains:

* correctness of the two tabulation combinators `CertKernel.tabArr` and `CertKernel.iterArr`
  and of the bounded quantifier `CertKernel.allB`;
* the translation `toE` of the sentinel arithmetic of the kernel (`INF` standing for `+∞`)
  into `ℕ∞`, which is the type in which the costs of Section 4.2 of the source are measured;
* two elementary estimates for the binary shifts used by the kernel's fixed-point arithmetic.
-/

open scoped BigOperators

namespace MaskedDigit

open CertKernel

/-! ## Arrays -/

theorem arrPush_getD_lt {α : Type _} (a : Array α) (x : α) (d : α) (i : ℕ) (h : i < a.size) :
    (a.push x).getD i d = a.getD i d := by
  simp only [Array.getD, Array.size_push, dif_pos h, dif_pos (Nat.lt_succ_of_lt h)]
  exact Array.getElem_push_lt _

theorem arrPush_getD_size {α : Type _} (a : Array α) (x : α) (d : α) (i : ℕ) (h : i = a.size) :
    (a.push x).getD i d = x := by
  subst h; simp [Array.getD, Array.size_push]

theorem tabArr_succ {α : Type _} (f : ℕ → α) (n : ℕ) :
    tabArr f (n + 1) = (tabArr f n).push (f n) := by
  simp [tabArr, List.range_succ]

theorem tabArr_size {α : Type _} (f : ℕ → α) : ∀ n, (tabArr f n).size = n
  | 0 => rfl
  | n + 1 => by rw [tabArr_succ]; simp [tabArr_size f n]

theorem tabArr_getD {α : Type _} (f : ℕ → α) (d : α) :
    ∀ {n i : ℕ}, i < n → (tabArr f n).getD i d = f i := by
  intro n
  induction n with
  | zero => intro i h; omega
  | succ k ih =>
      intro i h
      rw [tabArr_succ]
      rcases Nat.lt_or_ge i k with hk | hk
      · rw [arrPush_getD_lt _ _ _ _ (by rw [tabArr_size]; omega)]
        exact ih hk
      · have : i = k := by omega
        subst this
        exact arrPush_getD_size _ _ _ _ (by rw [tabArr_size])

theorem kernelIterArr_size {α : Type _} (f : α → α) (dflt a0 : α) :
    ∀ n, (iterArr f dflt a0 n).size = n + 1
  | 0 => rfl
  | n + 1 => by
      rw [iterArr]
      simp [kernelIterArr_size f dflt a0 n]

theorem kernelIterArr_getD {α : Type _} (f : α → α) (dflt a0 : α) :
    ∀ {n i : ℕ}, i ≤ n → (iterArr f dflt a0 n).getD i dflt = iterF f a0 i := by
  intro n
  induction n with
  | zero =>
      intro i h
      have : i = 0 := by omega
      subst this
      rfl
  | succ k ih =>
      intro i h
      rw [iterArr]
      rcases Nat.lt_or_ge i (k + 1) with hk | hk
      · rw [arrPush_getD_lt _ _ _ _ (by rw [kernelIterArr_size]; omega)]
        exact ih (by omega)
      · have hik : i = k + 1 := by omega
        subst hik
        rw [arrPush_getD_size _ _ _ _ (by rw [kernelIterArr_size]), ih (le_refl k)]
        rfl

/-! ## The bounded quantifier -/

theorem allB_spec {p : ℕ → Bool} : ∀ {n : ℕ}, allB p n = true → ∀ i, i < n → p i = true := by
  intro n
  induction n with
  | zero => intro _ i h; omega
  | succ k ih =>
      intro h i hi
      rw [allB, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge i k with hk | hk
      · exact ih h.2 i hk
      · have : i = k := by omega
        subst this; exact h.1

/-! ## The sentinel arithmetic -/

/-- The translation of the kernel's sentinel arithmetic into `ℕ∞`: the value `INF` (and
anything above it) stands for the cost `+∞` of Section 4.2 of `masked_digit_bound.tex`. -/
def toE (v : ℕ) : ℕ∞ := if INF ≤ v then ⊤ else (v : ℕ∞)

theorem toE_of_lt {v : ℕ} (h : v < INF) : toE v = (v : ℕ∞) := by
  simp [toE, Nat.not_le.2 h]

theorem toE_of_ge {v : ℕ} (h : INF ≤ v) : toE v = ⊤ := by simp [toE, h]

@[simp] theorem toE_zero : toE 0 = 0 := by
  rw [toE_of_lt (by norm_num [INF])]; rfl

theorem toE_mono {a b : ℕ} (h : a ≤ b) : toE a ≤ toE b := by
  unfold toE
  split_ifs with h1 h2 h2
  · exact le_refl _
  · omega
  · exact le_top
  · exact_mod_cast h

theorem toE_eq_top_iff {v : ℕ} : toE v = ⊤ ↔ INF ≤ v := by
  unfold toE
  split_ifs with h
  · exact iff_of_true rfl h
  · constructor
    · intro hv; exact absurd hv (by exact_mod_cast ENat.coe_ne_top v)
    · intro hv; omega

theorem toE_min (a b : ℕ) : toE (min a b) = min (toE a) (toE b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (toE_mono h)]
  · rw [min_eq_right h, min_eq_right (toE_mono h)]

/-- Splitting a cost is never cheaper: `toE a + toE b ≤ toE (a + b)`. -/
theorem toE_add_le (a b : ℕ) : toE a + toE b ≤ toE (a + b) := by
  by_cases h : INF ≤ a + b
  · rw [toE_of_ge h]; exact le_top
  · have ha : a < INF := by omega
    have hb : b < INF := by omega
    rw [toE_of_lt ha, toE_of_lt hb, toE_of_lt (by omega)]
    push_cast; ring_nf; rfl

/-- The converse inequality, under the hypothesis that the sentinel is not reached by
accident. -/
theorem toE_le_add {a b : ℕ} (h : a < INF → b < INF → a + b < INF) :
    toE (a + b) ≤ toE a + toE b := by
  by_cases ha : INF ≤ a
  · rw [toE_of_ge ha]; simp
  · by_cases hb : INF ≤ b
    · rw [toE_of_ge hb]; simp
    · have hab := h (by omega) (by omega)
      rw [toE_of_lt (by omega : a < INF), toE_of_lt (by omega : b < INF), toE_of_lt hab]
      push_cast; ring_nf; rfl

theorem epow_toE {x : ℝ} (v : ℕ) : epow x (toE v) = if INF ≤ v then 0 else x ^ v := by
  unfold toE
  split_ifs with h
  · simp
  · simp

/-! ## Shifts -/

theorem cast_shiftRight_le (n k : ℕ) : ((n >>> k : ℕ) : ℝ) ≤ (n : ℝ) / 2 ^ k := by
  rw [Nat.shiftRight_eq_div_pow]
  rw [le_div_iff₀ (by positivity)]
  have := Nat.div_mul_le_self n (2 ^ k)
  calc ((n / 2 ^ k : ℕ) : ℝ) * 2 ^ k = ((n / 2 ^ k * 2 ^ k : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (n : ℝ) := by exact_mod_cast this

theorem le_cast_ceilShift (n k : ℕ) : (n : ℝ) / 2 ^ k ≤ ((ceilShift n k : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  have hdiv : n >>> k = n / 2 ^ k := Nat.shiftRight_eq_div_pow n k
  rw [show ceilShift n k =
      if ((n >>> k) <<< k == n) = true then n >>> k else n >>> k + 1 from rfl]
  split_ifs with h
  · have h' : (n >>> k) <<< k = n := by simpa using h
    rw [Nat.shiftLeft_eq] at h'
    rw [hdiv] at h' ⊢
    exact_mod_cast h'.ge
  · rw [hdiv]
    have hp : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdm := Nat.div_add_mod n (2 ^ k)
    have hm : n % 2 ^ k < 2 ^ k := Nat.mod_lt n hp
    have hkey : n ≤ (n / 2 ^ k + 1) * 2 ^ k := by
      calc n = 2 ^ k * (n / 2 ^ k) + n % 2 ^ k := hdm.symm
        _ ≤ 2 ^ k * (n / 2 ^ k) + 2 ^ k := Nat.add_le_add_left hm.le _
        _ = (n / 2 ^ k + 1) * 2 ^ k := by ring
    exact_mod_cast hkey

end MaskedDigit
