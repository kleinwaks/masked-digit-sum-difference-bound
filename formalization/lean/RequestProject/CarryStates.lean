import RequestProject.ControlledSum

/-!
# The carry-state transfer operator

This file formalizes Section 4.2 ("The carry-state transfer operator") and Proposition 6
("Finite accessible-subgraph certificate") of `masked_digit_bound.tex`.

* `wcost` is the extended digit cost `w(d) = κ(d)` for `d ∈ D` and `+∞` otherwise;
* `aPlus`, `aMinus` are the arrays `A⁺_r = w(r)` and `A⁻_r = w(r - q)` of the source (the
  latter equals `w(q - r)` by evenness of `w`);
* `CostState` is the normalized cost-difference state `δ ∈ ℤ ∪ {-∞, +∞}`;
* `costStatePair` and `stateOfPair` are the two directions of the normalization;
* `carryStep` is the pair of updates of equation (29) (`eq:carry-transition`), and
  `carryIncr`, `carryNext` are the increment `a(δ, r)` and the new state `Φ(δ, r)`;
* `carryKernel` is the reachable-state kernel `T_x` of equation (30) (`eq:carry-operator`);
* `collatz_wielandt_pow` and `controlled_finite_graph_certificate` are the abstract content
  of Proposition 6.
-/

open scoped BigOperators
open Filter Topology

namespace MaskedDigit

namespace MaskData

variable (D : MaskData)

/-! ## The extended digit cost -/

/-- The extended digit cost `w(d) = κ(d)` for `d ∈ D = M - M` and `w(d) = +∞` otherwise,
introduced at the start of Section 4.2 of `masked_digit_bound.tex`. -/
noncomputable def wcost (d : ℤ) : ℕ∞ := if d ∈ D.diffSupport then (D.kappa d : ℕ∞) else ⊤

/-- `A⁺_r = w(r)` is the cost of the signed digit `r` (Section 4.2 of
`masked_digit_bound.tex`).  In particular `A⁺_q = +∞`. -/
noncomputable def aPlus (r : ℕ) : ℕ∞ := D.wcost (r : ℤ)

/-- `A⁻_r = w(r - q)` is the cost of the signed digit `r - q` (Section 4.2 of
`masked_digit_bound.tex`); by evenness of `w` this is the `w(q - r)` of the source.  In
particular `A⁻_q = w(0) = 0`. -/
noncomputable def aMinus (r : ℕ) : ℕ∞ := D.wcost ((r : ℤ) - (D.q : ℤ))

/-- By evenness of the witness cost `κ`, the cost `A⁻_r = w(r - q)` of Section 4.2 of `masked_digit_bound.tex` equals the `w(q - r)` written in the source. -/
theorem aMinus_eq (r : ℕ) : D.aMinus r = D.wcost ((D.q : ℤ) - (r : ℤ)) := by
  unfold aMinus wcost
  have hneg : ∀ d : ℤ, (d ∈ D.diffSupport) = ((-d) ∈ D.diffSupport) := by
    intro d
    apply propext
    constructor
    · exact fun h => D.neg_mem_diffSupport h
    · intro h; simpa using D.neg_mem_diffSupport h
  have h1 : ((r : ℤ) - (D.q : ℤ)) ∈ D.diffSupport ↔ ((D.q : ℤ) - (r : ℤ)) ∈ D.diffSupport := by
    rw [hneg ((r : ℤ) - (D.q : ℤ))]
    simp [neg_sub]
  by_cases h : ((r : ℤ) - (D.q : ℤ)) ∈ D.diffSupport
  · rw [if_pos h, if_pos (h1.1 h)]
    have : (D.q : ℤ) - (r : ℤ) = -((r : ℤ) - (D.q : ℤ)) := by ring
    rw [this, D.kappa_neg]
  · rw [if_neg h, if_neg (fun hc => h (h1.2 hc))]

/-- The boundary value `A⁺_q = +∞` of Section 4.2 of `masked_digit_bound.tex`: the digit `q` exceeds `B` and so is not a difference digit. -/
theorem aPlus_q : D.aPlus D.q = ⊤ := by
  unfold aPlus wcost
  rw [if_neg]
  intro hc
  have := D.abs_le_of_mem_diffSupport hc
  have hq : (D.B : ℤ) < (D.q : ℤ) := by exact_mod_cast D.q_gt_B
  rw [abs_le] at this
  omega

/-- The boundary value `A⁻_q = w(0) = 0` of Section 4.2 of `masked_digit_bound.tex`. -/
theorem aMinus_q : D.aMinus D.q = 0 := by
  unfold aMinus wcost
  have h : ((D.q : ℤ) - (D.q : ℤ)) = 0 := by ring
  rw [h, if_pos D.zero_mem_diffSupport, D.kappa_zero]
  rfl

/-! ## The normalized cost-difference state -/

/-- The normalized cost-difference state `δ ∈ ℤ ∪ {-∞, +∞}` of Section 4.2 of
`masked_digit_bound.tex`, recording which of the two representatives of a canonical prefix
residue is cheaper and by how much. -/
inductive CostState
  | finite : ℤ → CostState
  | negInf : CostState
  | posInf : CostState
  deriving DecidableEq

namespace CostState

/-- The normalized pair `(u₀, u₁)` determined by a state `δ`, as described in Section 4.2 of
`masked_digit_bound.tex`: `(0, δ)` for `0 ≤ δ < +∞`, `(-δ, 0)` for `-∞ < δ < 0`,
`(0, +∞)` for `δ = +∞`, and `(+∞, 0)` for `δ = -∞`. -/
def toPair : CostState → ℕ∞ × ℕ∞
  | finite d => if 0 ≤ d then (0, (d.toNat : ℕ∞)) else (((-d).toNat : ℕ∞), 0)
  | negInf => (⊤, 0)
  | posInf => (0, ⊤)

/-- The state `δ = u₁ - u₀` determined by a normalized pair, with the conventions
`δ = +∞` when `u₁ = +∞` and `δ = -∞` when `u₀ = +∞` (Section 4.2 of
`masked_digit_bound.tex`).  The value at `(+∞, +∞)` is never used, since at least one of the
two costs is finite. -/
def ofPair : ℕ∞ → ℕ∞ → CostState
  | ⊤, ⊤ => posInf
  | ⊤, (_ : ℕ) => negInf
  | (_ : ℕ), ⊤ => posInf
  | (m : ℕ), (n : ℕ) => finite ((n : ℤ) - (m : ℤ))

end CostState

/-- The pair of updates of equation (29) (`eq:carry-transition`) of
`masked_digit_bound.tex`: on appending the canonical digit `r`,
`v₀ = min(u₀ + A⁺_r, u₁ + A⁺_{r+1})` and `v₁ = min(u₀ + A⁻_r, u₁ + A⁻_{r+1})`. -/
noncomputable def carryStep (delta : CostState) (r : ℕ) : ℕ∞ × ℕ∞ :=
  let u := delta.toPair
  (min (u.1 + D.aPlus r) (u.2 + D.aPlus (r + 1)),
   min (u.1 + D.aMinus r) (u.2 + D.aMinus (r + 1)))

/-- The increment `a(δ, r) = min(v₀, v₁)` of Section 4.2 of `masked_digit_bound.tex`. -/
noncomputable def carryIncr (delta : CostState) (r : ℕ) : ℕ∞ :=
  min (D.carryStep delta r).1 (D.carryStep delta r).2

/-- The new state `Φ(δ, r) = v₁ - v₀` of Section 4.2 of `masked_digit_bound.tex`. -/
noncomputable def carryNext (delta : CostState) (r : ℕ) : CostState :=
  CostState.ofPair (D.carryStep delta r).1 (D.carryStep delta r).2

/-- The reachable-state kernel `T_x(δ, δ') = ∑_{r < q, Φ(δ,r) = δ'} x^{a(δ,r)}` of
equation (30) (`eq:carry-operator`) of `masked_digit_bound.tex`, with `x^{+∞} = 0`. -/
noncomputable def carryKernel (x : ℝ) (delta delta' : CostState) : ℝ :=
  ∑ r ∈ (Finset.range D.q).filter (fun r => D.carryNext delta r = delta'),
    (if D.carryIncr delta r = ⊤ then 0 else x ^ (D.carryIncr delta r).toNat)

/-- The initial state of the empty prefix is `+∞`, since `C₀⁽⁰⁾(0) = 0` and
`C₀⁽¹⁾(0) = +∞` (Section 4.2 of `masked_digit_bound.tex`). -/
def carryInit : CostState := CostState.posInf

/-! ## Proposition 6: the finite accessible-subgraph certificate -/

/-- Powers of a nonnegative matrix are nonnegative. -/
theorem matrix_pow_nonneg {sigma : Type} [Fintype sigma] [DecidableEq sigma]
    (T : Matrix sigma sigma ℝ) (hT : ∀ i j, 0 ≤ T i j) : ∀ (n : ℕ) (i j : sigma),
      0 ≤ (T ^ n) i j := by
  intro n
  induction n with
  | zero => intro i j; simp only [pow_zero, Matrix.one_apply]; split <;> norm_num
  | succ m ihm =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (ihm i l) (hT l j)

/-- **Iterated Collatz--Wielandt bound.**  If `T` is a nonnegative matrix, `v` is a positive
vector and `T v ≥ c v` componentwise, then `Tⁿ v ≥ cⁿ v` componentwise.  This is the
elementary step in the proof of Proposition 6 of `masked_digit_bound.tex` that avoids
formalizing complex eigenvalues. -/
theorem collatz_wielandt_pow {sigma : Type} [Fintype sigma] [DecidableEq sigma]
    (T : Matrix sigma sigma ℝ) (hT : ∀ i j, 0 ≤ T i j) (v : sigma → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hcw : ∀ i, c * v i ≤ ∑ j, T i j * v j) :
    ∀ (n : ℕ) (i : sigma), c ^ n * v i ≤ ∑ j, (T ^ n) i j * v j := by
  intro n
  induction n with
  | zero => intro i; simp [Matrix.one_apply, Finset.sum_ite_eq]
  | succ n ih =>
    intro i
    calc c ^ (n + 1) * v i = c ^ n * (c * v i) := by ring
      _ ≤ c ^ n * ∑ j, T i j * v j := by
          exact mul_le_mul_of_nonneg_left (hcw i) (pow_nonneg hc n)
      _ = ∑ j, T i j * (c ^ n * v j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ ∑ j, T i j * (∑ l, (T ^ n) j l * v l) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (ih j) (hT i j)
      _ = ∑ l, ((T ^ (n + 1)) i l) * v l := by
          rw [pow_succ']
          simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

/-- **Proposition 6 (Finite accessible-subgraph certificate)** of `masked_digit_bound.tex`,
in the positive-vector (Collatz--Wielandt) form of equation (32)
(`eq:controlled-collatz`).

The hypothesis `haccess` is the path-restriction inequality obtained in the source by
retaining, in the path expansion (31) of `Z_{h+n}(x)`, only the paths that reach the finite
accessible set `F` after `h` steps and remain in `F` for the next `n` steps; `b` is the
vector of entrance weights `b_s = (T_x^h)(+∞, s) > 0`. -/
theorem controlled_finite_graph_certificate {sigma : Type} [Fintype sigma] [DecidableEq sigma]
    [Nonempty sigma] (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (T : Matrix sigma sigma ℝ) (hT : ∀ i j, 0 ≤ T i j)
    (v : sigma → ℝ) (c : ℝ) (hv : ∀ i, 0 < v i) (hc : 0 < c)
    (hcw : ∀ i, c * v i ≤ ∑ j, T i j * v j)
    (b : sigma → ℝ) (hb : ∀ i, 0 < b i) (h : ℕ)
    (haccess : ∀ n : ℕ, ∑ i, b i * (∑ j, (T ^ n) i j) ≤ D.Zminus x (h + n)) :
    Real.log c ≤ D.PminusPressure x := by
  classical
  have hune : (Finset.univ : Finset sigma).Nonempty := Finset.univ_nonempty
  obtain ⟨i0, -⟩ := hune
  -- the extreme values of the positive certificate vector
  set vmax : ℝ := Finset.univ.sup' Finset.univ_nonempty v with hvmaxdef
  set vmin : ℝ := Finset.univ.inf' Finset.univ_nonempty v with hvmindef
  have hvmax_ge : ∀ i, v i ≤ vmax := fun i => Finset.le_sup' v (Finset.mem_univ i)
  have hvmin_le : ∀ i, vmin ≤ v i := fun i => Finset.inf'_le v (Finset.mem_univ i)
  have hvmax0 : 0 < vmax := lt_of_lt_of_le (hv i0) (hvmax_ge i0)
  have hvmin0 : 0 < vmin := (Finset.lt_inf'_iff _).2 (fun i _ => hv i)
  have hTn : ∀ (n : ℕ) (i j : sigma), 0 ≤ (T ^ n) i j := matrix_pow_nonneg T hT
  -- the iterated Collatz--Wielandt inequality gives a lower bound for each row sum
  have hrow : ∀ (n : ℕ) (i : sigma), c ^ n * (vmin / vmax) ≤ ∑ j, (T ^ n) i j := by
    intro n i
    have hcw' := collatz_wielandt_pow T hT v c hc.le hcw n i
    have hup : ∑ j, (T ^ n) i j * v j ≤ vmax * ∑ j, (T ^ n) i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      calc (T ^ n) i j * v j ≤ (T ^ n) i j * vmax :=
            mul_le_mul_of_nonneg_left (hvmax_ge j) (hTn n i j)
        _ = vmax * (T ^ n) i j := mul_comm _ _
    have hlow : c ^ n * vmin ≤ vmax * ∑ j, (T ^ n) i j := by
      have : c ^ n * vmin ≤ c ^ n * v i :=
        mul_le_mul_of_nonneg_left (hvmin_le i) (pow_nonneg hc.le n)
      linarith
    rw [← mul_div_assoc, div_le_iff₀ hvmax0]
    nlinarith [hlow]
  -- entrance weights convert this into a lower bound for `Z_{h+n}(x)`
  set K0 : ℝ := (∑ i, b i) * (vmin / vmax) with hK0def
  have hK00 : 0 < K0 :=
    mul_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty) (div_pos hvmin0 hvmax0)
  have hZ : ∀ n : ℕ, K0 * c ^ n ≤ D.Zminus x (h + n) := by
    intro n
    refine le_trans ?_ (haccess n)
    have hterm : ∀ i : sigma, b i * (c ^ n * (vmin / vmax)) ≤ b i * ∑ j, (T ^ n) i j :=
      fun i => mul_le_mul_of_nonneg_left (hrow n i) (hb i).le
    calc K0 * c ^ n = ∑ i, b i * (c ^ n * (vmin / vmax)) := by
          rw [hK0def, ← Finset.sum_mul]
          ring
      _ ≤ ∑ i, b i * ∑ j, (T ^ n) i j := Finset.sum_le_sum fun i _ => hterm i
  have hlogZ : ∀ n : ℕ, Real.log K0 + (n : ℝ) * Real.log c
      ≤ Real.log (D.Zminus x (h + n)) := by
    intro n
    have h1 : Real.log (K0 * c ^ n) ≤ Real.log (D.Zminus x (h + n)) :=
      Real.log_le_log (by positivity) (hZ n)
    rwa [Real.log_mul (ne_of_gt hK00) (by positivity), Real.log_pow] at h1
  -- pass to the limit
  have hlim1 : Tendsto (fun n : ℕ => ((n : ℝ) * Real.log c + Real.log K0) /
      ((h : ℝ) + (n : ℝ) * 1)) atTop (𝓝 (Real.log c)) := by
    simpa using tendsto_affine_ratio (Real.log c) (Real.log K0) (h : ℝ) 1 one_pos
  have hlim2 : Tendsto (fun n : ℕ => Real.log (D.Zminus x (h + n)) / ((h + n : ℕ) : ℝ)) atTop
      (𝓝 (D.PminusPressure x)) := by
    have htend := D.tendsto_PminusPressure hx0 hx1
    have hmap : Tendsto (fun n : ℕ => h + n) atTop atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_add_left n h) Filter.tendsto_id
    exact htend.comp hmap
  refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hX : (0 : ℝ) < ((h + n : ℕ) : ℝ) := by
    have : 0 < h + n := by omega
    exact_mod_cast this
  have hden : (h : ℝ) + (n : ℝ) * 1 = ((h + n : ℕ) : ℝ) := by push_cast; ring
  rw [hden]
  refine (div_le_div_iff_of_pos_right hX).2 ?_
  have := hlogZ n
  linarith

/-- The combination of Proposition 6 with Lemma 4, equation (32) (`eq:controlled-collatz`) of
`masked_digit_bound.tex`: a positive-vector certificate for the difference operator yields a
lower bound for `C₃ₐ`. -/
theorem controlled_collatz_bound {sigma : Type} [Fintype sigma] [DecidableEq sigma]
    [Nonempty sigma] (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (T : Matrix sigma sigma ℝ) (hT : ∀ i j, 0 ≤ T i j)
    (v : sigma → ℝ) (c : ℝ) (hv : ∀ i, 0 < v i) (hc : 0 < c)
    (hcw : ∀ i, c * v i ≤ ∑ j, T i j * v j)
    (b : sigma → ℝ) (hb : ∀ i, 0 < b i) (h : ℕ)
    (haccess : ∀ n : ℕ, ∑ i, b i * (∑ j, (T ^ n) i j) ≤ D.Zminus x (h + n)) :
    1 + (Real.log c - Real.log (D.Pplus x)) / Real.log D.q ≤ C3a := by
  have hlog := D.controlled_finite_graph_certificate x hx0 hx1 T hT v c hv hc hcw b hb h haccess
  have hmain := D.controlled_pressure_bound x hx0 hx1
  have hq : (1 : ℝ) < (D.q : ℝ) := by
    have : 1 < D.q := lt_of_le_of_lt D.B_pos D.q_gt_B
    exact_mod_cast this
  have hlogq : 0 < Real.log D.q := Real.log_pos hq
  refine le_trans ?_ hmain
  gcongr

end MaskData

end MaskedDigit
