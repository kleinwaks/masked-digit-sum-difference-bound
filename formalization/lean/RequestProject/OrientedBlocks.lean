import RequestProject.CoreConstruction

/-!
# Positional orientation of a self-inverse residue

This file supplies the one ingredient of the proof of Proposition 3
(`prop:controlled-block`, the controlled-carry block bound) of `masked_digit_bound.tex` that
the first formalization of that proposition skipped: the treatment of the nonzero
self-inverse residue `h = q^k / 2`.

In the source the alphabet of block residues is the whole attainable set `𝒜_k`, including
`h`.  Since `-h = h` modulo `q^k`, the minimum-cost digit block `d(h)` chosen for `h` cannot
be paired with the block of another residue in order to cancel the unweighted digit sum.
The source instead makes the type count `N_h^{(ℓ)} = 2⌊ℓ p_h / 2⌋` even and orients half of
the occurrences of `h` in each residue word as `d(h)` and half as `-d(h)`, *by a
deterministic rule based only on their positions*.

Here that rule is realized as follows.  The occurrences of `h` in a residue word are ordered
from left to right, and consecutive occurrences are paired off: the occurrence of index `m`
in this left-to-right ordering is oriented as `d(h)` if `m` is even and as `-d(h)` if `m` is
odd (`Oriented.osign`).  When the number of occurrences of `h` is even — which is the
condition imposed on the words that are kept, exactly as the source makes `N_h^{(ℓ)}` even —
precisely half of the occurrences carry `d(h)` and half carry `-d(h)`, and their
contributions to the unweighted digit sum cancel exactly
(`Oriented.sum_osign_eq_zero_of_even`).  Their contributions to the cost budget cancel as
well, since `κ` is even, so both orientations have the same cost
(`MaskData.blockCost_odig`).

The rule depends only on the residue word, so the digit blocks of a word are a function of
the word; and since `d(h)` and `-d(h)` have the same residue modulo `q^k`, the residues of
the oriented blocks are still the letters of the word.  Consequently the encoding of a word
by the integer it represents remains injective
(`Oriented.oriented_word_injective`), which is the property that makes the construction
produce distinct differences.

The main result is `MaskData.core_bound_oriented`, the oriented version of
`MaskData.core_bound`: it allows one letter `hh` of the alphabet to be its own negation, and
therefore retains *every* attainable residue in the partition sum.
-/

open scoped BigOperators

namespace MaskedDigit

namespace Oriented

variable {A : Type*} [DecidableEq A]

/-- The number of occurrences of the self-inverse letter `hh` strictly before position `j`
in the (ℕ-indexed) word `u`.  This is the left-to-right index of the occurrence at `j`, used
to orient it in the proof of Proposition 3 of `masked_digit_bound.tex`. -/
def cnt (hh : A) (u : ℕ → A) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, (if u i = hh then 1 else 0)

@[simp] theorem cnt_zero (hh : A) (u : ℕ → A) : cnt hh u 0 = 0 := by simp [cnt]

theorem cnt_succ (hh : A) (u : ℕ → A) (j : ℕ) :
    cnt hh u (j + 1) = cnt hh u j + (if u j = hh then 1 else 0) := by
  rw [cnt, cnt, Finset.sum_range_succ]

/-- Peeling the first letter: the occurrence index shifts by the contribution of position
`0`. -/
theorem cnt_shift (hh : A) (u : ℕ → A) (j : ℕ) :
    cnt hh u (j + 1) = (if u 0 = hh then 1 else 0) + cnt hh (fun t => u (t + 1)) j := by
  simp only [cnt]
  rw [Finset.sum_range_succ' (fun i => if u i = hh then 1 else 0) j]
  ring

/-- **The positional orientation rule.**  The occurrence of the self-inverse letter `hh` at
position `j` of the word `u` is oriented positively when its left-to-right index (shifted by
the offset `m`) is even, and negatively when it is odd; every other letter keeps its own
digit block.  This is the deterministic, position-based rule of the proof of Proposition 3
of `masked_digit_bound.tex`, which orients half of the occurrences of `h` as `d(h)` and half
as `-d(h)`. -/
def osign (hh : A) (u : ℕ → A) (m j : ℕ) : ℤ :=
  if u j = hh then (-1 : ℤ) ^ (m + cnt hh u j) else 1

theorem osign_eq_one_or_neg_one (hh : A) (u : ℕ → A) (m j : ℕ) :
    osign hh u m j = 1 ∨ osign hh u m j = -1 := by
  unfold osign
  split
  · rcases Nat.even_or_odd (m + cnt hh u j) with he | ho
    · exact Or.inl he.neg_one_pow
    · exact Or.inr ho.neg_one_pow
  · exact Or.inl rfl

theorem osign_ne_zero (hh : A) (u : ℕ → A) (m j : ℕ) : osign hh u m j ≠ 0 := by
  rcases osign_eq_one_or_neg_one hh u m j with h | h <;> rw [h] <;> norm_num

theorem osign_of_ne (hh : A) {u : ℕ → A} {m j : ℕ} (h : u j ≠ hh) : osign hh u m j = 1 := by
  simp [osign, h]

@[simp] theorem osign_zero (hh : A) (u : ℕ → A) (m : ℕ) :
    osign hh u m 0 = if u 0 = hh then (-1 : ℤ) ^ m else 1 := by
  simp [osign]

/-- The orientation of a position depends only on the letters up to that position, so it is
unchanged when the first letter is peeled off (with the offset updated). -/
theorem osign_shift (hh : A) (u : ℕ → A) (m j : ℕ) :
    osign hh u m (j + 1)
      = osign hh (fun t => u (t + 1)) (m + (if u 0 = hh then 1 else 0)) j := by
  unfold osign
  by_cases h : u (j + 1) = hh
  · have h' : (fun t => u (t + 1)) j = hh := h
    rw [if_pos h, if_pos h', cnt_shift hh u j]
    congr 1
    ring
  · have h' : ¬ ((fun t => u (t + 1)) j = hh) := h
    rw [if_neg h, if_neg h']

/-- **Exact cancellation of the two orientations.**  The alternating signs attached to the
occurrences of `hh` sum to zero as soon as the number of occurrences is even; this is the
statement that half of the occurrences are oriented as `d(h)` and half as `-d(h)`, as in the
proof of Proposition 3 of `masked_digit_bound.tex`. -/
theorem sum_osign_aux (hh : A) (u : ℕ → A) (l : ℕ) :
    ∑ j ∈ Finset.range l, (if u j = hh then ((-1 : ℤ)) ^ (cnt hh u j) else 0)
      = if Even (cnt hh u l) then 0 else 1 := by
  induction l with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, cnt_succ]
    by_cases h : u n = hh
    · rw [if_pos h, if_pos h]
      rcases Nat.even_or_odd (cnt hh u n) with he | ho
      · rw [if_pos he, he.neg_one_pow]
        have : ¬ Even (cnt hh u n + 1) := by simp [Nat.even_add_one, he]
        rw [if_neg this]
        ring
      · have hne : ¬ Even (cnt hh u n) := by simpa [Nat.not_even_iff_odd] using ho
        rw [if_neg hne, ho.neg_one_pow]
        have : Even (cnt hh u n + 1) := by simp [Nat.even_add_one, hne]
        rw [if_pos this]
        ring
    · rw [if_neg h, if_neg h]
      simp

theorem sum_osign_eq_zero_of_even (hh : A) (u : ℕ → A) {l : ℕ} (hev : Even (cnt hh u l)) :
    ∑ j ∈ Finset.range l, (if u j = hh then ((-1 : ℤ)) ^ (cnt hh u j) else 0) = 0 := by
  rw [sum_osign_aux hh u l, if_pos hev]

/-- The extension of a word of length `l` to an ℕ-indexed word, used to express the
positional orientation rule. -/
def extend (hh : A) {l : ℕ} (w : Fin l → A) : ℕ → A := fun m => if h : m < l then w ⟨m, h⟩ else hh

omit [DecidableEq A] in
@[simp] theorem extend_coe (hh : A) {l : ℕ} (w : Fin l → A) (j : Fin l) :
    extend hh w (j : ℕ) = w j := by
  simp [extend, j.isLt]

/-- **Injectivity of oriented residue words.**  Two words of blocks that represent the same
integer are equal, even though the self-inverse letter `hh` may occur with either of its two
orientations: the orientation is a function of the word, and both orientations of `hh` have
the same residue.  This is the injectivity step of the proof of Proposition 3 of
`masked_digit_bound.tex` ("the orientation chosen for `h` does not change its residue"). -/
theorem oriented_word_injective_aux (Q : ℕ) (hQ : 0 < Q) (val : A → ℤ) (hh : A)
    (hinj : Function.Injective fun a => ((val a : ℤ) : ZMod Q))
    (hres : ((val hh : ℤ) : ZMod Q) = -((val hh : ℤ) : ZMod Q)) :
    ∀ (l m : ℕ) (u u' : ℕ → A),
      (∑ j ∈ Finset.range l, osign hh u m j * val (u j) * (Q : ℤ) ^ j
        = ∑ j ∈ Finset.range l, osign hh u' m j * val (u' j) * (Q : ℤ) ^ j) →
      ∀ j < l, u j = u' j := by
  have hQ0 : (0 : ℤ) < (Q : ℤ) := by exact_mod_cast hQ
  -- the residue of an oriented block is the residue of the letter
  have hVres : ∀ (u : ℕ → A) (m j : ℕ),
      ((osign hh u m j * val (u j) : ℤ) : ZMod Q) = ((val (u j) : ℤ) : ZMod Q) := by
    intro u m j
    by_cases h : u j = hh
    · rcases osign_eq_one_or_neg_one hh u m j with hs | hs
      · rw [hs, one_mul]
      · rw [hs, h]
        push_cast
        linear_combination -hres
    · rw [osign_of_ne hh h, one_mul]
  intro l
  induction l with
  | zero => intro m u u' _ j hj; omega
  | succ n ih =>
    intro m u u' hval j hj
    rw [Finset.sum_range_succ' (fun j => osign hh u m j * val (u j) * (Q : ℤ) ^ j) n,
      Finset.sum_range_succ' (fun j => osign hh u' m j * val (u' j) * (Q : ℤ) ^ j) n] at hval
    simp only [pow_succ, pow_zero, mul_one] at hval
    have h1 : ∀ (f : ℕ → A),
        ∑ i ∈ Finset.range n, osign hh f m (i + 1) * val (f (i + 1)) * ((Q : ℤ) ^ i * (Q : ℤ))
          = (∑ i ∈ Finset.range n, osign hh f m (i + 1) * val (f (i + 1)) * (Q : ℤ) ^ i)
            * (Q : ℤ) := by
      intro f; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1 u, h1 u'] at hval
    have hdvd : (Q : ℤ) ∣ (osign hh u m 0 * val (u 0) - osign hh u' m 0 * val (u' 0)) :=
      ⟨(∑ i ∈ Finset.range n, osign hh u' m (i + 1) * val (u' (i + 1)) * (Q : ℤ) ^ i)
        - (∑ i ∈ Finset.range n, osign hh u m (i + 1) * val (u (i + 1)) * (Q : ℤ) ^ i),
        by linarith [hval]⟩
    have hz : ((osign hh u m 0 * val (u 0) - osign hh u' m 0 * val (u' 0) : ℤ) : ZMod Q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (by exact_mod_cast hdvd)
    have hVV : ((osign hh u m 0 * val (u 0) : ℤ) : ZMod Q)
        = ((osign hh u' m 0 * val (u' 0) : ℤ) : ZMod Q) := by
      push_cast at hz ⊢
      linear_combination hz
    have h0 : u 0 = u' 0 := by
      refine hinj ?_
      show ((val (u 0) : ℤ) : ZMod Q) = ((val (u' 0) : ℤ) : ZMod Q)
      rw [← hVres u m 0, ← hVres u' m 0]
      exact hVV
    have hsgn : osign hh u m 0 = osign hh u' m 0 := by
      rw [osign_zero, osign_zero, h0]
    have hVeq : osign hh u m 0 * val (u 0) = osign hh u' m 0 * val (u' 0) := by
      rw [hsgn, h0]
    have hshift : ∑ i ∈ Finset.range n, osign hh u m (i + 1) * val (u (i + 1)) * (Q : ℤ) ^ i
        = ∑ i ∈ Finset.range n, osign hh u' m (i + 1) * val (u' (i + 1)) * (Q : ℤ) ^ i := by
      rw [hVeq] at hval
      exact mul_right_cancel₀ (ne_of_gt hQ0) (by linarith [hval])
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact h0
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      set m' := m + (if u 0 = hh then 1 else 0) with hm'
      have hu : ∀ i, osign hh u m (i + 1) = osign hh (fun t => u (t + 1)) m' i := by
        intro i; rw [hm', osign_shift]
      have hu' : ∀ i, osign hh u' m (i + 1) = osign hh (fun t => u' (t + 1)) m' i := by
        intro i
        rw [osign_shift]
        rw [hm', h0]
      have hshift' :
          ∑ i ∈ Finset.range n, osign hh (fun t => u (t + 1)) m' i * val (u (i + 1)) * (Q : ℤ) ^ i
            = ∑ i ∈ Finset.range n,
                osign hh (fun t => u' (t + 1)) m' i * val (u' (i + 1)) * (Q : ℤ) ^ i := by
        rw [← Finset.sum_congr rfl (fun i _ => by rw [hu i] :
              ∀ i ∈ Finset.range n,
                osign hh u m (i + 1) * val (u (i + 1)) * (Q : ℤ) ^ i
                  = osign hh (fun t => u (t + 1)) m' i * val (u (i + 1)) * (Q : ℤ) ^ i),
          ← Finset.sum_congr rfl (fun i _ => by rw [hu' i] :
              ∀ i ∈ Finset.range n,
                osign hh u' m (i + 1) * val (u' (i + 1)) * (Q : ℤ) ^ i
                  = osign hh (fun t => u' (t + 1)) m' i * val (u' (i + 1)) * (Q : ℤ) ^ i)]
        exact hshift
      exact ih m' (fun t => u (t + 1)) (fun t => u' (t + 1)) hshift' j' (by omega)

end Oriented

/-! ## Parity of the number of occurrences under the product weights -/

namespace ProductWeights

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The signed generating identity `E[(-1)^{#\{j : w_j = h\}}] = (1 - 2 p_h)^ℓ` for the
product (Gibbs) measure on words.  It is the quantitative form of the statement that the
number of occurrences of the self-inverse residue can be taken even, as required by the type
count `N_h^{(ℓ)} = 2⌊ℓ p_h/2⌋` of the proof of Proposition 3 of
`masked_digit_bound.tex`. -/
theorem sum_wt_sign (p : A → ℝ) (hsum : ∑ a, p a = 1) (hh : A) (l : ℕ) :
    ∑ w : Fin l → A, wt p w * (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0))
      = (1 - 2 * p hh) ^ l := by
  classical
  set F : Fin l → A → ℝ := fun _ a => p a * (if a = hh then -1 else 1) with hF
  have hprod : ∀ w : Fin l → A,
      ∏ j, F j (w j) = wt p w * (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0)) := by
    intro w
    simp only [hF, wt, Finset.prod_mul_distrib]
    congr 1
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun j _ => by by_cases h : w j = hh <;> simp [h]
  have hsumF : ∀ j : Fin l, ∑ a, F j a = 1 - 2 * p hh := by
    intro j
    have : ∀ a : A, F j a = p a - 2 * (if a = hh then p a else 0) := by
      intro a
      by_cases h : a = hh
      · simp [hF, h]; ring
      · simp [hF, h]
    rw [Finset.sum_congr rfl (fun a _ => this a), Finset.sum_sub_distrib, hsum, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ hh p]
    simp
  calc ∑ w : Fin l → A, wt p w * (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0))
      = ∑ w : Fin l → A, ∏ j, F j (w j) := (Finset.sum_congr rfl fun w _ => (hprod w).symm)
    _ = ∏ j, ∑ a, F j a := (Fintype.prod_sum F).symm
    _ = (1 - 2 * p hh) ^ l := by simp [hsumF]

/-- **The words with an even number of occurrences of `h` carry at least a quarter of the
mass**, as soon as `ℓ` is large enough that `|1 - 2 p_h|^ℓ ≤ 1/2`.  This is what makes the
even type count `N_h^{(ℓ)} = 2⌊ℓ p_h/2⌋` of the proof of Proposition 3 of
`masked_digit_bound.tex` admissible. -/
theorem quarter_le_sum_wt_even (p : A → ℝ) (hsum : ∑ a, p a = 1) (hh : A)
    (l : ℕ) (hr : |1 - 2 * p hh| ^ l ≤ 1 / 2) :
    (1 : ℝ) / 4 ≤ ∑ w ∈ Finset.univ.filter
      (fun w : Fin l → A => Even (∑ j, (if w j = hh then 1 else 0))), wt p w := by
  classical
  set E : Finset (Fin l → A) :=
    Finset.univ.filter (fun w : Fin l → A => Even (∑ j, (if w j = hh then 1 else 0))) with hE
  have htot : ∑ w : Fin l → A, wt p w = 1 := sum_wt p hsum l
  have hsig : ∑ w : Fin l → A, wt p w * (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0))
      = (1 - 2 * p hh) ^ l := sum_wt_sign p hsum hh l
  have hsplit : ∑ w : Fin l → A, wt p w * (1 + (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0)))
      = 2 * ∑ w ∈ E, wt p w := by
    have hterm : ∀ w : Fin l → A,
        wt p w * (1 + (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0)))
          = if Even (∑ j, (if w j = hh then 1 else 0)) then 2 * wt p w else 0 := by
      intro w
      rcases Nat.even_or_odd (∑ j, (if w j = hh then 1 else 0)) with he | ho
      · rw [if_pos he, he.neg_one_pow]; ring
      · have hne : ¬ Even (∑ j, (if w j = hh then 1 else 0)) := by
          simpa [Nat.not_even_iff_odd] using ho
        rw [if_neg hne, ho.neg_one_pow]; ring
    rw [Finset.sum_congr rfl (fun w _ => hterm w), hE, Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by split <;> simp
  have hexp : ∑ w : Fin l → A, wt p w * (1 + (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0)))
      = 1 + (1 - 2 * p hh) ^ l := by
    have : ∀ w : Fin l → A, wt p w * (1 + (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0)))
        = wt p w + wt p w * (-1 : ℝ) ^ (∑ j, (if w j = hh then 1 else 0)) := by
      intro w; ring
    rw [Finset.sum_congr rfl (fun w _ => this w), Finset.sum_add_distrib, htot, hsig]
  have habs : -(1 / 2 : ℝ) ≤ (1 - 2 * p hh) ^ l := by
    have h1 : |(1 - 2 * p hh) ^ l| ≤ 1 / 2 := by rw [abs_pow]; exact hr
    have := abs_le.1 h1
    linarith [this.1]
  have : 2 * ∑ w ∈ E, wt p w = 1 + (1 - 2 * p hh) ^ l := by rw [← hsplit, hexp]
  linarith

end ProductWeights

namespace Oriented

variable {A : Type*} [DecidableEq A]

/-- **Injectivity of oriented residue words**, finite-vector form; see
`oriented_word_injective_aux`.  Since the orientation of the self-inverse letter is a
function of the word alone, and both orientations have the same residue, distinct words give
distinct integers, exactly as in the proof of Proposition 3 of `masked_digit_bound.tex`. -/
theorem oriented_word_injective (Q : ℕ) (hQ : 0 < Q) (val : A → ℤ) (hh : A)
    (hinj : Function.Injective fun a => ((val a : ℤ) : ZMod Q))
    (hres : ((val hh : ℤ) : ZMod Q) = -((val hh : ℤ) : ZMod Q)) (l : ℕ) :
    Function.Injective (fun w : Fin l → A =>
      ∑ j : Fin l, osign hh (extend hh w) 0 (j : ℕ) * val (w j) * (Q : ℤ) ^ (j : ℕ)) := by
  intro w w' hww
  have e : ∀ v : Fin l → A,
      ∑ j : Fin l, osign hh (extend hh v) 0 (j : ℕ) * val (v j) * (Q : ℤ) ^ (j : ℕ)
        = ∑ i ∈ Finset.range l,
            osign hh (extend hh v) 0 i * val (extend hh v i) * (Q : ℤ) ^ i := by
    intro v
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => osign hh (extend hh v) 0 i * val (extend hh v i) * (Q : ℤ) ^ i) l]
    exact Finset.sum_congr rfl fun j _ => by rw [extend_coe]
  simp only at hww
  rw [e w, e w'] at hww
  funext j
  have h := oriented_word_injective_aux Q hQ val hh hinj hres l 0 (extend hh w) (extend hh w')
    hww (j : ℕ) j.isLt
  rwa [extend_coe, extend_coe] at h

/-- The signed digit blocks of a word: the block of the letter `w j`, oriented by the
positional rule `osign`.  This is the digit array attached to a residue word in the proof of
Proposition 3 of `masked_digit_bound.tex`. -/
def odig (k : ℕ) (vec : A → Fin k → ℤ) (hh : A) {l : ℕ} (w : Fin l → A)
    (j : Fin l) (i : Fin k) : ℤ :=
  osign hh (extend hh w) 0 (j : ℕ) * vec (w j) i

theorem odig_eq_smul (k : ℕ) (vec : A → Fin k → ℤ) (hh : A) {l : ℕ} (w : Fin l → A)
    (j : Fin l) :
    odig k vec hh w j = fun i => osign hh (extend hh w) 0 (j : ℕ) * vec (w j) i := rfl

end Oriented

namespace MaskData

variable (D : MaskData)

/-- The oriented blocks are signed difference digits, since the digit set `D = M - M` is
symmetric. -/
theorem odig_mem {A : Type*} [DecidableEq A] (k : ℕ) (vec : A → Fin k → ℤ)
    (hvec : ∀ a i, vec a i ∈ D.diffSupport) (hh : A) {l : ℕ} (w : Fin l → A)
    (j : Fin l) (i : Fin k) : Oriented.odig k vec hh w j i ∈ D.diffSupport := by
  rcases Oriented.osign_eq_one_or_neg_one hh (Oriented.extend hh w) 0 (j : ℕ) with hs | hs
  · simp only [Oriented.odig, hs, one_mul]
    exact hvec _ _
  · simp only [Oriented.odig, hs, neg_one_mul]
    exact D.neg_mem_diffSupport (hvec _ _)

/-- **The two orientations of a block have the same cost.**  This is the statement of the
proof of Proposition 3 of `masked_digit_bound.tex` that "its negative has the same cost", and
it is what makes the contributions of the two orientations to the cost budget cancel. -/
theorem blockCost_odig {A : Type*} [DecidableEq A] (k : ℕ) (vec : A → Fin k → ℤ) (hh : A)
    {l : ℕ} (w : Fin l → A) (j : Fin l) :
    D.blockCost k (Oriented.odig k vec hh w j) = D.blockCost k (vec (w j)) := by
  rcases Oriented.osign_eq_one_or_neg_one hh (Oriented.extend hh w) 0 (j : ℕ) with hs | hs
  · simp only [blockCost, Oriented.odig, hs, one_mul]
  · simp only [blockCost, Oriented.odig, hs, neg_one_mul]
    exact Finset.sum_congr rfl fun i _ => D.kappa_neg _

/-- **The two orientations of a block have the same residue.**  This is the statement of the
proof of Proposition 3 of `masked_digit_bound.tex` that "the orientation chosen for `h` does
not change its residue" (its value is negated, and `-h = h` modulo `q^k`). -/
theorem blockVal_odig {A : Type*} [DecidableEq A] (k : ℕ) (vec : A → Fin k → ℤ) (hh : A)
    {l : ℕ} (w : Fin l → A) (j : Fin l) :
    D.blockVal k (Oriented.odig k vec hh w j)
      = Oriented.osign hh (Oriented.extend hh w) 0 (j : ℕ) * D.blockVal k (vec (w j)) := by
  simp only [blockVal, Oriented.odig, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem blockSum_odig {A : Type*} [DecidableEq A] (k : ℕ) (vec : A → Fin k → ℤ) (hh : A)
    {l : ℕ} (w : Fin l → A) (j : Fin l) :
    blockSum k (Oriented.odig k vec hh w j)
      = Oriented.osign hh (Oriented.extend hh w) 0 (j : ℕ) * blockSum k (vec (w j)) := by
  simp only [blockSum, Oriented.odig, Finset.mul_sum]

/-- **Exact cancellation of the two orientations in the digit budget.**  If the number of
occurrences of the self-inverse letter `hh` in the word is even, then the unweighted digit
sum of the oriented word is exactly the unweighted digit sum of the other letters: the
occurrences of `hh` contribute `d(h)` and `-d(h)` in equal numbers.  This is the step of the
proof of Proposition 3 of `masked_digit_bound.tex` where "the two orientations at `h` cancel
in the same way". -/
theorem sum_blockSum_odig {A : Type*} [DecidableEq A] (k : ℕ) (vec : A → Fin k → ℤ) (hh : A)
    {l : ℕ} (w : Fin l → A) (hev : Even (∑ j, (if w j = hh then 1 else 0))) :
    ∑ j, blockSum k (Oriented.odig k vec hh w j)
      = ∑ j : Fin l, (if w j = hh then 0 else blockSum k (vec (w j))) := by
  classical
  set u := Oriented.extend hh w with hu
  have hcnt : Oriented.cnt hh u l = ∑ j : Fin l, (if w j = hh then 1 else 0) := by
    rw [Oriented.cnt, ← Fin.sum_univ_eq_sum_range (fun i => if u i = hh then 1 else 0) l]
    exact (Finset.sum_congr rfl fun j _ => by rw [hu, Oriented.extend_coe]).symm
  have hterm : ∀ j : Fin l, blockSum k (Oriented.odig k vec hh w j)
      = (if w j = hh then 0 else blockSum k (vec (w j)))
        + blockSum k (vec hh) * (if w j = hh then ((-1 : ℤ)) ^ (Oriented.cnt hh u (j : ℕ))
            else 0) := by
    intro j
    rw [blockSum_odig, ← hu]
    by_cases h : w j = hh
    · have hu' : u (j : ℕ) = hh := by rw [hu, Oriented.extend_coe]; exact h
      rw [if_pos h, if_pos h, h, Oriented.osign, if_pos hu']
      simp only [Nat.zero_add]
      ring
    · have hu' : ¬ (u (j : ℕ) = hh) := by rw [hu, Oriented.extend_coe]; exact h
      rw [if_neg h, if_neg h, Oriented.osign, if_neg hu']
      ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.mul_sum]
  have hzero : ∑ j : Fin l, (if w j = hh then ((-1 : ℤ)) ^ (Oriented.cnt hh u (j : ℕ)) else 0)
      = 0 := by
    have hconv : ∑ j : Fin l, (if w j = hh then ((-1 : ℤ)) ^ (Oriented.cnt hh u (j : ℕ)) else 0)
        = ∑ i ∈ Finset.range l, (if u i = hh then ((-1 : ℤ)) ^ (Oriented.cnt hh u i) else 0) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => if u i = hh then ((-1 : ℤ)) ^ (Oriented.cnt hh u i) else 0) l]
      exact Finset.sum_congr rfl fun j _ => by rw [hu, Oriented.extend_coe]
    rw [hconv]
    exact Oriented.sum_osign_eq_zero_of_even hh u (by rw [hcnt]; exact hev)
  rw [hzero, mul_zero, add_zero]

/-- A sum over a union is at most the sum of the two sums, for a nonnegative summand. -/
theorem sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) : ∑ a ∈ s ∪ t, f a ≤ ∑ a ∈ s, f a + ∑ a ∈ t, f a := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ a ∈ s ∩ t, f a := Finset.sum_nonneg fun a _ => hf a
  linarith

/-! ## The oriented core construction -/

set_option maxHeartbeats 4000000 in
/-- **The core digit construction, with a positionally oriented self-inverse letter.**

This is the oriented refinement of `MaskData.core_bound`.  The alphabet `A` of signed digit
blocks is closed under an involution `neg` with `vec (neg a) = -vec a`, *except* at one
distinguished letter `hh`, which is its own negation (`neg hh = hh`) and whose block may have
a nonzero value; all that is required of it is that its two orientations `vec hh` and
`-vec hh` have the same residue modulo `q ^ k` (hypothesis `hhres`).  This is precisely the
situation of the nonzero self-inverse residue `h = q^k/2` in the proof of Proposition 3
(`prop:controlled-block`) of `masked_digit_bound.tex`, which the unoriented construction has
to discard.

The proof follows the source: the occurrences of `hh` in each residue word are ordered from
left to right and oriented alternately as `d(h)` and `-d(h)`, only words with an even number
of occurrences of `hh` are kept (the even type count `N_h^{(ℓ)} = 2⌊ℓp_h/2⌋` of the source),
so that exactly half of the occurrences carry each orientation and their contributions to
both digit budgets cancel exactly; the orientation depends only on the residue word, so the
injection of words into `U - U` is unaffected.

The conclusion is the same as for `core_bound`, but now the partition sum
`Z = ∑_{a ∈ A} x^{cost(a)}` runs over the *whole* alphabet, `hh` included. -/
theorem core_bound_oriented (k : ℕ) (hk : 0 < k) {A : Type} [Fintype A] [DecidableEq A]
    [Nontrivial A]
    (vec : A → Fin k → ℤ) (hvec : ∀ a i, vec a i ∈ D.diffSupport)
    (neg : A → A) (hneginv : Function.Involutive neg)
    (hh : A) (hnegh : neg hh = hh)
    (hneg : ∀ a, a ≠ hh → vec (neg a) = -vec a)
    (hhres : ((D.blockVal k (vec hh) : ℤ) : ZMod (D.q ^ k))
      = -((D.blockVal k (vec hh) : ℤ) : ZMod (D.q ^ k)))
    (hinj : Function.Injective fun a => ((D.blockVal k (vec a) : ℤ) : ZMod (D.q ^ k)))
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (Pp C : ℝ) (hPp0 : 0 < Pp) (hC0 : 0 < C)
    (hPp : ∀ m T : ℕ, ((D.sumSet m T).card : ℝ) * x ^ T ≤ C * Pp ^ m) :
    1 + (Real.log (∑ a : A, x ^ D.blockCost k (vec a)) / k - Real.log Pp) /
        Real.log D.q ≤ C3a := by
  classical
  -- the cost and the (corrected) digit sum of a block, the partition function and the weights
  set c : A → ℕ := fun a => D.blockCost k (vec a) with hcdef
  set sd : A → ℤ := fun a => if a = hh then 0 else blockSum k (vec a) with hsddef
  set Z : ℝ := ∑ a, x ^ c a with hZdef
  have hZ0 : 0 < Z := ProductWeights.gibbs_partition_pos hx0 c
  set p : A → ℝ := ProductWeights.gibbs x c with hpdef
  have hp0 : ∀ a, 0 ≤ p a := fun a => ProductWeights.gibbs_nonneg hx0 c a
  have hppos : ∀ a, 0 < p a := by
    intro a
    rw [hpdef, ProductWeights.gibbs]
    exact div_pos (pow_pos hx0 _) (ProductWeights.gibbs_partition_pos hx0 c)
  have hpsum : ∑ a, p a = 1 := ProductWeights.sum_gibbs hx0 c
  set mu : ℝ := ∑ a, p a * (c a : ℝ) with hmudef
  have hmu0 : 0 ≤ mu := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (Nat.cast_nonneg _)
  have hq1 : 1 < D.q := by have := D.q_gt_B; have := D.B_pos; omega
  have hqR : (1 : ℝ) < (D.q : ℝ) := by exact_mod_cast hq1
  have hlogq : 0 < Real.log D.q := Real.log_pos hqR
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlogx : Real.log x < 0 := Real.log_neg hx0 hx1
  -- the weight of the self-inverse letter is strictly between `0` and `1`
  have hphh1 : p hh < 1 := by
    obtain ⟨b, hb⟩ := exists_ne hh
    have hpair : p hh + p b ≤ ∑ a, p a := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({hh, b} : Finset A)) (fun a _ _ => hp0 a)
      rwa [Finset.sum_pair (Ne.symm hb)] at h
    have := hppos b
    linarith [hpsum]
  have hrlt : |1 - 2 * p hh| < 1 := by
    rw [abs_lt]
    constructor
    · linarith
    · linarith [hppos hh]
  have hrev : ∀ᶠ l : ℕ in Filter.atTop, |1 - 2 * p hh| ^ l ≤ 1 / 2 := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (1 - 2 * p hh)) hrlt
    exact h.eventually_le_const (by norm_num)
  -- the two centred statistics of the construction
  set g1 : A → ℝ := fun a => (c a : ℝ) - mu with hg1def
  set g2 : A → ℝ := fun a => (sd a : ℝ) with hg2def
  have hg1c : ∑ a, p a * g1 a = 0 := by
    simp only [hg1def, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum, ← hmudef]
    ring
  have hcneg : ∀ a, c (neg a) = c a := by
    intro a
    by_cases ha : a = hh
    · rw [ha, hnegh]
    · simp only [hcdef, blockCost, hneg a ha, Pi.neg_apply]
      exact Finset.sum_congr rfl fun i _ => D.kappa_neg _
  have hsdneg : ∀ a, sd (neg a) = - sd a := by
    intro a
    by_cases ha : a = hh
    · rw [ha, hnegh]
      simp only [hsddef, if_pos rfl, neg_zero]
    · have hna : neg a ≠ hh := by
        intro hcon
        apply ha
        have h := congrArg neg hcon
        rwa [hneginv a, hnegh] at h
      simp only [hsddef]
      rw [if_neg hna, if_neg ha, hneg a ha]
      simp [blockSum]
  have hpneg : ∀ a, p (neg a) = p a := by
    intro a; simp only [hpdef, ProductWeights.gibbs, hcneg a]
  have hg2c : ∑ a, p a * g2 a = 0 := by
    have h1 : ∑ a, p (neg a) * g2 (neg a) = ∑ a, p a * g2 a :=
      Equiv.sum_comp hneginv.toPerm (fun a => p a * g2 a)
    have h2 : ∀ a, p (neg a) * g2 (neg a) = -(p a * g2 a) := by
      intro a; rw [hpneg a]; simp only [hg2def, hsdneg a]; push_cast; ring
    rw [Finset.sum_congr rfl (fun a _ => h2 a), Finset.sum_neg_distrib] at h1
    linarith
  -- if the claimed bound does not exceed `1`, it is trivial
  rcases le_or_gt (Real.log Z / k - Real.log Pp) 0 with hdel | hdel
  · have h1 : (Real.log Z / k - Real.log Pp) / Real.log D.q ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hdel hlogq.le
    linarith [one_le_C3a]
  set delta : ℝ := Real.log Z / (k : ℝ) - Real.log Pp with hdeltadef
  have hdelta0 : 0 < delta := hdel
  -- the key estimate, for each admissible `ε`
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have claim : ∀ eps : ℝ, 0 < eps → 0 < (k : ℝ) * delta + 3 * eps * Real.log x →
      1 + ((k : ℝ) * delta + 3 * eps * Real.log x) / ((k : ℝ) * Real.log D.q) ≤ C3a := by
    intro eps heps0 hKpos
    set K : ℝ := (k : ℝ) * delta + 3 * eps * Real.log x with hKdef
    set c0 : ℝ := (2 + 2 * (D.B : ℝ)) * Real.log x - Real.log 8 - Real.log C with hc0def
    set V1 : ℝ := ∑ a, p a * g1 a ^ 2 with hV1def
    set V2 : ℝ := ∑ a, p a * g2 a ^ 2 with hV2def
    have hV1n : 0 ≤ V1 := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (sq_nonneg _)
    have hV2n : 0 ≤ V2 := Finset.sum_nonneg fun a _ => mul_nonneg (hp0 a) (sq_nonneg _)
    have hQpos : 0 < D.q ^ k := pow_pos (by omega) k
    -- the oriented digit blocks of a word are signed difference digits
    have hdg : ∀ {l : ℕ} (w : Fin l → A) (j : Fin l) (i : Fin k),
        Oriented.odig k vec hh w j i ∈ D.diffSupport := fun w j i => D.odig_mem k vec hvec hh w j i
    -- a word of blocks is determined by the integer it represents
    have hwordinj : ∀ l : ℕ, Function.Injective
        (fun w : Fin l → A => D.wordVal k (Oriented.odig k vec hh w) (fun j => j)) := by
      intro l w w' hww
      have e : ∀ v : Fin l → A, D.wordVal k (Oriented.odig k vec hh v) (fun j => j)
          = ∑ j : Fin l, Oriented.osign hh (Oriented.extend hh v) 0 (j : ℕ)
              * D.blockVal k (vec (v j)) * ((D.q ^ k : ℕ) : ℤ) ^ (j : ℕ) := by
        intro v
        rw [wordVal]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [D.blockVal_odig k vec hh v j]
        push_cast
        ring
      have hoinj := Oriented.oriented_word_injective (D.q ^ k) hQpos
        (fun a => D.blockVal k (vec a)) hh hinj hhres l
      apply hoinj
      simp only
      rw [← e w, ← e w']
      exact hww
    -- the estimate for all large numbers of blocks
    have key : ∀ᶠ l : ℕ in Filter.atTop,
        1 + ((l : ℝ) * K + c0) / (Real.log 5 + (l : ℝ) * ((k : ℝ) * Real.log D.q)) ≤ C3a := by
      obtain ⟨N1, hN1⟩ := exists_nat_gt (8 * (V1 + V2) / eps ^ 2)
      obtain ⟨N2, hN2⟩ := exists_nat_gt ((-c0) / K)
      obtain ⟨N3, hN3⟩ := Filter.eventually_atTop.1 hrev
      rw [Filter.eventually_atTop]
      refine ⟨max (max (max N1 N2) N3) 1, fun l hl => ?_⟩
      have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hl
      have hl0 : 0 < l := hl1
      have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl0
      have hlN1 : 8 * (V1 + V2) / eps ^ 2 < (l : ℝ) := by
        refine lt_of_lt_of_le hN1 ?_
        have h : N1 ≤ l :=
          le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hl
        exact_mod_cast h
      have hlN2 : (-c0) / K < (l : ℝ) := by
        refine lt_of_lt_of_le hN2 ?_
        have h : N2 ≤ l :=
          le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hl
        exact_mod_cast h
      have hrl : |1 - 2 * p hh| ^ l ≤ 1 / 2 :=
        hN3 l (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hl)
      have hepsl : (0 : ℝ) < eps * (l : ℝ) := by positivity
      -- the good set of words: both statistics are concentrated, and the number of
      -- occurrences of the self-inverse letter is even
      set E : Finset (Fin l → A) := Finset.univ.filter
        (fun w : Fin l → A => Even (∑ j, (if w j = hh then 1 else 0))) with hEdef
      set G : Finset (Fin l → A) := Finset.univ.filter
        (fun w => (|∑ j, g1 (w j)| < eps * (l : ℝ) ∧ |∑ j, g2 (w j)| < eps * (l : ℝ)) ∧
          Even (∑ j, (if w j = hh then 1 else 0))) with hGdef
      -- the good set carries at least an eighth of the mass
      have hnn : ∀ w : Fin l → A, 0 ≤ ProductWeights.wt p w :=
        fun w => ProductWeights.wt_nonneg hp0 w
      have hmass : (1 : ℝ) / 8 ≤ ∑ w ∈ G, ProductWeights.wt p w := by
        have hbad1 := ProductWeights.mass_deviation_le p hp0 hpsum g1 hg1c l hepsl
        have hbad2 := ProductWeights.mass_deviation_le p hp0 hpsum g2 hg2c l hepsl
        have hE4 : (1 : ℝ) / 4 ≤ ∑ w ∈ E, ProductWeights.wt p w :=
          ProductWeights.quarter_le_sum_wt_even p hpsum hh l hrl
        set Bad1 : Finset (Fin l → A) :=
          Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g1 (w j)|) with hBad1
        set Bad2 : Finset (Fin l → A) :=
          Finset.univ.filter (fun w : Fin l → A => eps * (l : ℝ) ≤ |∑ j, g2 (w j)|) with hBad2
        have hsub : E ⊆ G ∪ (Bad1 ∪ Bad2) := by
          intro w hw
          simp only [hEdef, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          simp only [hGdef, hBad1, hBad2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and]
          by_cases h1 : |∑ j, g1 (w j)| < eps * (l : ℝ)
          · by_cases h2 : |∑ j, g2 (w j)| < eps * (l : ℝ)
            · exact Or.inl ⟨⟨h1, h2⟩, hw⟩
            · exact Or.inr (Or.inr (not_lt.1 h2))
          · exact Or.inr (Or.inl (not_lt.1 h1))
        have hle1 : ∑ w ∈ E, ProductWeights.wt p w
            ≤ ∑ w ∈ G ∪ (Bad1 ∪ Bad2), ProductWeights.wt p w :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => hnn w)
        have hle2 : ∑ w ∈ G ∪ (Bad1 ∪ Bad2), ProductWeights.wt p w
            ≤ (∑ w ∈ G, ProductWeights.wt p w)
              + ((∑ w ∈ Bad1, ProductWeights.wt p w) + ∑ w ∈ Bad2, ProductWeights.wt p w) := by
          refine le_trans (sum_union_le_of_nonneg hnn) ?_
          have := sum_union_le_of_nonneg (s := Bad1) (t := Bad2) hnn
          linarith
        have hnum : ((l : ℝ) * V1) / (eps * (l : ℝ)) ^ 2 + ((l : ℝ) * V2) / (eps * (l : ℝ)) ^ 2
            ≤ 1 / 8 := by
          rw [← add_div, div_le_iff₀ (by positivity)]
          have h5 : 8 * (V1 + V2) < eps ^ 2 * (l : ℝ) := by
            rw [div_lt_iff₀ (by positivity)] at hlN1
            linarith
          nlinarith [hlR]
        linarith
      -- the digit budget
      set L : ℕ := ⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ + D.B with hLdef
      have hLB : D.B ≤ L := Nat.le_add_left _ _
      have hyn : (0 : ℝ) ≤ (mu + 2 * eps) * (l : ℝ) / 2 := by
        apply div_nonneg _ (by norm_num)
        exact mul_nonneg (by linarith) hlR.le
      have hceil : ((⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ : ℕ) : ℝ) < (mu + 2 * eps) * (l : ℝ) / 2 + 1 :=
        Nat.ceil_lt_add_one hyn
      have hceil' : (mu + 2 * eps) * (l : ℝ) / 2 ≤ ((⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ : ℕ) : ℝ) :=
        Nat.le_ceil _
      -- the digit sums of a good word obey the budget
      have hg1sum : ∀ w : Fin l → A,
          ∑ j, g1 (w j) = ((∑ j, c (w j) : ℕ) : ℝ) - mu * (l : ℝ) := by
        intro w
        simp only [hg1def]
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        ring
      have hg2sum : ∀ w : Fin l → A, ∑ j, g2 (w j) = ((∑ j, sd (w j) : ℤ) : ℝ) := by
        intro w
        simp only [hg2def]
        push_cast
        ring
      have hbudget : ∀ w ∈ G,
          (∑ t, D.wordAlpha k (Oriented.odig k vec hh w) (fun j => j) t) ≤ L ∧
            (∑ t, D.wordBeta k (Oriented.odig k vec hh w) (fun j => j) t) ≤ L := by
        intro w hw
        rw [hGdef, Finset.mem_filter] at hw
        obtain ⟨-, ⟨hw1, hw2⟩, hev⟩ := hw
        rw [hg1sum w, abs_lt] at hw1
        rw [hg2sum w, abs_lt] at hw2
        obtain ⟨hw1a, hw1b⟩ := hw1
        obtain ⟨hw2a, hw2b⟩ := hw2
        have hcostid : (∑ t, D.wordAlpha k (Oriented.odig k vec hh w) (fun j => j) t)
            + (∑ t, D.wordBeta k (Oriented.odig k vec hh w) (fun j => j) t)
            = ∑ j, c (w j) := by
          rw [D.sum_wordAlpha_add_sum_wordBeta k (Oriented.odig k vec hh w) (hdg w) (fun j => j)]
          exact Finset.sum_congr rfl fun j _ => D.blockCost_odig k vec hh w j
        have hdiffid : ((∑ t, D.wordAlpha k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℤ)
            - ((∑ t, D.wordBeta k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℤ)
            = ∑ j, sd (w j) := by
          rw [D.sum_wordAlpha_sub_sum_wordBeta k (Oriented.odig k vec hh w) (hdg w) (fun j => j),
            sum_blockSum_odig k vec hh w hev]
        have h1 : ((∑ t, D.wordAlpha k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℝ)
            + ((∑ t, D.wordBeta k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℝ)
            = ((∑ j, c (w j) : ℕ) : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcostid
        have h2 : ((∑ t, D.wordAlpha k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℝ)
            - ((∑ t, D.wordBeta k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℝ)
            = ((∑ j, sd (w j) : ℤ) : ℝ) := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hdiffid
        have hLR : (L : ℝ) = ((⌈(mu + 2 * eps) * (l : ℝ) / 2⌉₊ : ℕ) : ℝ) + (D.B : ℝ) := by
          rw [hLdef]; push_cast; ring
        have hB0 : (0 : ℝ) ≤ (D.B : ℝ) := Nat.cast_nonneg _
        constructor
        · have hA : ((∑ t, D.wordAlpha k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℝ)
              ≤ (L : ℝ) := by rw [hLR]; linarith
          exact_mod_cast hA
        · have hB : ((∑ t, D.wordBeta k (Oriented.odig k vec hh w) (fun j => j) t : ℕ) : ℝ)
              ≤ (L : ℝ) := by rw [hLR]; linarith
          exact_mod_cast hB
      -- the good words inject into the difference set
      have hGdiff : (G.card : ℝ)
          ≤ ((natDiffFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card : ℝ) := by
        have hcard : G.card ≤ (natDiffFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card := by
          refine Finset.card_le_card_of_injOn
            (fun w => D.wordVal k (Oriented.odig k vec hh w) (fun j => j)) ?_ ?_
          · intro w hw
            obtain ⟨hA, hB⟩ := hbudget w hw
            simp only [natDiffFinset, Finset.mem_coe]
            rw [← D.flatInt_wordAlpha_sub_flatInt_wordBeta k (Oriented.odig k vec hh w) (hdg w)
              (fun j => j)]
            exact Finset.mem_image₂_of_mem (f := fun (a b : ℕ) => (a : ℤ) - (b : ℤ))
              (D.flatInt_mem_maskSet _
                (fun t => D.wordAlpha_mem k (Oriented.odig k vec hh w) (hdg w) (fun j => j) t) hA)
              (D.flatInt_mem_maskSet _
                (fun t => D.wordBeta_mem k (Oriented.odig k vec hh w) (hdg w) (fun j => j) t) hB)
          · intro w _ w' _ h
            exact hwordinj l h
        exact_mod_cast hcard
      -- the lower bound for the difference set
      set nd : ℝ := Z ^ l / (8 * x ^ ((mu - eps) * (l : ℝ))) with hnddef
      have hxrpow : (0 : ℝ) < x ^ ((mu - eps) * (l : ℝ)) := Real.rpow_pos_of_pos hx0 _
      have hnd0 : 0 < nd := by rw [hnddef]; positivity
      have hcardnd : nd ≤ (G.card : ℝ) := by
        have hW0 : (0 : ℝ) < x ^ ((mu - eps) * (l : ℝ)) / Z ^ l := by positivity
        have hwtle : ∀ w ∈ G,
            ProductWeights.wt p w ≤ x ^ ((mu - eps) * (l : ℝ)) / Z ^ l := by
          intro w hw
          rw [hGdef, Finset.mem_filter] at hw
          obtain ⟨-, ⟨hw1, -⟩, -⟩ := hw
          rw [hg1sum w, abs_lt] at hw1
          have hexp : (mu - eps) * (l : ℝ) ≤ ((∑ j, c (w j) : ℕ) : ℝ) := by linarith [hw1.1]
          have hpow : x ^ (((∑ j, c (w j) : ℕ)) : ℝ) ≤ x ^ ((mu - eps) * (l : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le hexp
          rw [Real.rpow_natCast] at hpow
          rw [hpdef, ProductWeights.wt_gibbs, ← hZdef]
          gcongr
        have hsumle : ∑ w ∈ G, ProductWeights.wt p w
            ≤ (G.card : ℝ) * (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) := by
          calc ∑ w ∈ G, ProductWeights.wt p w
              ≤ ∑ _w ∈ G, (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) := Finset.sum_le_sum hwtle
            _ = (G.card : ℝ) * (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hmul : nd * (x ^ ((mu - eps) * (l : ℝ)) / Z ^ l) = 1 / 8 := by
          rw [hnddef]
          field_simp
        refine le_of_mul_le_mul_right ?_ hW0
        rw [hmul]
        linarith
      -- the upper bound for the sumset
      set E2 : ℝ := (mu + 2 * eps) * (l : ℝ) + 2 + 2 * (D.B : ℝ) with hE2def
      have h2L : ((2 * L : ℕ) : ℝ) ≤ E2 := by
        rw [hLdef, hE2def]
        push_cast
        linarith
      have hxE : (0 : ℝ) < x ^ E2 := Real.rpow_pos_of_pos hx0 _
      set ns : ℝ := C * Pp ^ (l * k) / x ^ E2 with hnsdef
      have hns0 : 0 < ns := by rw [hnsdef]; positivity
      have hnsle : ((natSumFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card : ℝ) ≤ ns := by
        have h1 : ((natSumFinset (D.maskSet (l * k) L) (D.maskSet (l * k) L)).card : ℝ)
            ≤ ((D.sumSet (l * k) (2 * L)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (D.natSumFinset_maskSet_subset (l * k) L)
        have h2 := hPp (l * k) (2 * L)
        have h3 : x ^ E2 ≤ x ^ ((2 * L : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le h2L
        rw [Real.rpow_natCast] at h3
        have h4 : ((D.sumSet (l * k) (2 * L)).card : ℝ) ≤ C * Pp ^ (l * k) / x ^ (2 * L) := by
          rw [le_div_iff₀ (pow_pos hx0 _)]
          exact h2
        have h5 : C * Pp ^ (l * k) / x ^ (2 * L) ≤ ns := by
          rw [hnsdef]
          gcongr
        linarith
      -- the logarithm of the ratio
      have hlognd : Real.log nd
          = (l : ℝ) * Real.log Z - Real.log 8 - ((mu - eps) * (l : ℝ)) * Real.log x := by
        rw [hnddef, Real.log_div (by positivity) (by positivity), Real.log_pow,
          Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0]
        ring
      have hlogns : Real.log ns
          = Real.log C + ((l * k : ℕ) : ℝ) * Real.log Pp - E2 * Real.log x := by
        rw [hnsdef, Real.log_div (by positivity) (by positivity),
          Real.log_mul (ne_of_gt hC0) (by positivity), Real.log_pow, Real.log_rpow hx0]
      have hlogval : Real.log (nd / ns) = (l : ℝ) * K + c0 := by
        rw [Real.log_div (ne_of_gt hnd0) (ne_of_gt hns0), hlognd, hlogns, hKdef, hc0def, hE2def,
          hdeltadef]
        push_cast
        field_simp
        ring
      have hnum0 : 0 ≤ (l : ℝ) * K + c0 := by
        rw [div_lt_iff₀ hKpos] at hlN2
        linarith
      have hratio : 1 ≤ nd / ns := by
        have hlog : 0 ≤ Real.log (nd / ns) := by rw [hlogval]; exact hnum0
        exact (Real.log_nonneg_iff (by positivity)).1 hlog
      have hfin := D.ghr_from_maskSet_estimates (m := l * k) (L := L)
        (Nat.mul_pos hl0 hk) hLB nd ns hnd0 hns0 (le_trans hcardnd hGdiff) hnsle hratio
      rw [hlogval] at hfin
      have hcast : ((l * k : ℕ) : ℝ) * Real.log D.q = (l : ℝ) * ((k : ℝ) * Real.log D.q) := by
        push_cast; ring
      rw [hcast] at hfin
      exact hfin
    have hlim : Filter.Tendsto
        (fun l : ℕ => 1 + ((l : ℝ) * K + c0) / (Real.log 5 + (l : ℝ) * ((k : ℝ) * Real.log D.q)))
        Filter.atTop (nhds (1 + K / ((k : ℝ) * Real.log D.q))) :=
      tendsto_const_nhds.add
        (tendsto_affine_ratio K c0 (Real.log 5) ((k : ℝ) * Real.log D.q) (mul_pos hkR hlogq))
    exact le_of_tendsto hlim key
  -- let `ε → 0`
  refine le_of_forall_pos_le_add ?_
  intro eta heta
  set lx : ℝ := -Real.log x with hlxdef
  have hlx0 : 0 < lx := by rw [hlxdef]; linarith
  set eps : ℝ := min ((k : ℝ) * delta / (6 * lx)) (eta * ((k : ℝ) * Real.log D.q) / (6 * lx))
    with hepsdef
  have heps0 : 0 < eps := by
    refine lt_min ?_ ?_
    · have : 0 < (k : ℝ) * delta := mul_pos hkR hdelta0
      positivity
    · have : 0 < eta * ((k : ℝ) * Real.log D.q) := by positivity
      positivity
  have h6lx : (0 : ℝ) < 6 * lx := by linarith
  have heps1 : eps * (6 * lx) ≤ (k : ℝ) * delta := by
    have := min_le_left ((k : ℝ) * delta / (6 * lx)) (eta * ((k : ℝ) * Real.log D.q) / (6 * lx))
    rw [← hepsdef] at this
    rwa [le_div_iff₀ h6lx] at this
  have heps2 : eps * (6 * lx) ≤ eta * ((k : ℝ) * Real.log D.q) := by
    have := min_le_right ((k : ℝ) * delta / (6 * lx)) (eta * ((k : ℝ) * Real.log D.q) / (6 * lx))
    rw [← hepsdef] at this
    rwa [le_div_iff₀ h6lx] at this
  have hK : 0 < (k : ℝ) * delta + 3 * eps * Real.log x := by
    have hkd : 0 < (k : ℝ) * delta := mul_pos hkR hdelta0
    have : 3 * eps * Real.log x = -(eps * (6 * lx)) / 2 := by rw [hlxdef]; ring
    rw [this]
    linarith
  have hmain := claim eps heps0 hK
  -- rewrite the bound and absorb the error into `η`
  have hQ0 : (0 : ℝ) < (k : ℝ) * Real.log D.q := mul_pos hkR hlogq
  have hsplit : ((k : ℝ) * delta + 3 * eps * Real.log x) / ((k : ℝ) * Real.log D.q)
      = delta / Real.log D.q - (3 * eps * lx) / ((k : ℝ) * Real.log D.q) := by
    rw [hlxdef]
    field_simp
    ring
  have hfrac : (3 * eps * lx) / ((k : ℝ) * Real.log D.q) ≤ eta := by
    rw [div_le_iff₀ hQ0]
    have hA : 0 < eps * lx := mul_pos heps0 hlx0
    linarith
  rw [hsplit] at hmain
  linarith

end MaskData

end MaskedDigit
