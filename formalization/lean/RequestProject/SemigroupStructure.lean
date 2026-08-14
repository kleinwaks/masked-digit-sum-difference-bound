import RequestProject.FiniteDepth

/-!
# Semigroup structure of the carry-free mask

This file formalizes the concrete assertions of Section 6 ("Semigroup structure and
computational motivation") of `masked_digit_bound.tex`:

* the simple-gluing description `C_{a,b,r,s} = a⟨r,s⟩ + bℕ = ⟨ar, as, b⟩` of a numerical
  semigroup, and its instance `C = ⟨506, 508, 529⟩ = 23⟨22, 23⟩ + 508ℕ` (equation (37),
  `eq:column-gluing`), with the two relation degrees `ars = 11638` and `ab = 11684`;
* the column Frobenius number `23(22·23 − 22 − 23) + 22·508 = 21779`;
* the `2 × 3` generator grid `{3,4} × {506,508,529}` of equation (38) (`eq:grid`), the exact
  row relations `4(3c) = 3(4c)` and their degrees `6072, 6096, 6348`, and the two lifted
  column relations at `11638` and `13800`;
* the cheap near relations of equation (39) (`eq:grid-residual`), giving the explicit bounds
  `κ(2) ≤ 7098`, `κ(21) ≤ 7259`, `κ(23) ≤ 7245`, contrasted with the exact value
  `κ(1) = 14351`;
* the conductor `28922` of the full six-generator semigroup.

The remaining material of Section 6 (the Hilbert series of a simple gluing, the table of
previously explored masks, and the heuristic design principles) is either a statement about
generating functions that is not used anywhere in the source, or is explicitly described
there as computational evidence rather than as a proved assertion.
-/

open scoped BigOperators

namespace MaskedDigit

/-! ## Simple gluings of numerical semigroups -/

/-- **The simple-gluing description of Section 6 of `masked_digit_bound.tex`:**
`a⟨r,s⟩ + bℕ = ⟨ar, as, b⟩`.  The left-hand side is the set of all `a x + b y` with
`x ∈ ⟨r,s⟩` and `y ∈ ℕ`. -/
theorem gluing_eq_closure (a b r s : ℕ) :
    {n : ℕ | ∃ x ∈ AddSubmonoid.closure ({r, s} : Set ℕ), ∃ y : ℕ, n = a * x + b * y}
      = (AddSubmonoid.closure ({a * r, a * s, b} : Set ℕ) : Set ℕ) := by
  ext n
  simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, rfl⟩
    have hax : a * x ∈ AddSubmonoid.closure ({a * r, a * s, b} : Set ℕ) := by
      induction hx using AddSubmonoid.closure_induction with
      | mem z hz =>
          rcases hz with rfl | rfl
          · exact AddSubmonoid.subset_closure (by simp)
          · exact AddSubmonoid.subset_closure (by simp)
      | zero => simp
      | add u v _ _ hu hv =>
          have : a * (u + v) = a * u + a * v := by ring
          rw [this]
          exact add_mem hu hv
    have hby : b * y ∈ AddSubmonoid.closure ({a * r, a * s, b} : Set ℕ) := by
      have hb : b ∈ AddSubmonoid.closure ({a * r, a * s, b} : Set ℕ) :=
        AddSubmonoid.subset_closure (by simp)
      have hy := nsmul_mem hb y
      simpa [smul_eq_mul, mul_comm] using hy
    exact add_mem hax hby
  · intro hn
    induction hn using AddSubmonoid.closure_induction with
    | mem z hz =>
        rcases hz with rfl | rfl | rfl
        · exact ⟨r, AddSubmonoid.subset_closure (by simp), 0, by ring⟩
        · exact ⟨s, AddSubmonoid.subset_closure (by simp), 0, by ring⟩
        · exact ⟨0, zero_mem _, 1, by ring⟩
    | zero => exact ⟨0, zero_mem _, 0, by ring⟩
    | add u v _ _ hu hv =>
        obtain ⟨x₁, hx₁, y₁, rfl⟩ := hu
        obtain ⟨x₂, hx₂, y₂, rfl⟩ := hv
        exact ⟨x₁ + x₂, add_mem hx₁ hx₂, y₁ + y₂, by ring⟩

/-! ## The column semigroup `C = ⟨506, 508, 529⟩` -/

/-- The column generators `{506, 508, 529}` of Section 6 of `masked_digit_bound.tex`. -/
def columnGeneratorsList : List ℕ := [506, 508, 529]

/-- The parameters `(r, s, a, b) = (22, 23, 23, 508)` of the simple gluing (36)
(`eq:column-gluing`) of `masked_digit_bound.tex`. -/
theorem column_gluing_parameters :
    23 * 22 = 506 ∧ 23 * 23 = 529 ∧ (508 : ℕ) = 21 * 22 + 2 * 23 := by norm_num

/-- The coprimality conditions `gcd(r,s) = gcd(a,b) = 1` and the membership `b ∈ ⟨r,s⟩` of the
simple gluing (36) (`eq:column-gluing`) of `masked_digit_bound.tex`. -/
theorem column_gluing_conditions :
    Nat.gcd 22 23 = 1 ∧ Nat.gcd 23 508 = 1 ∧
      (508 : ℕ) ∈ AddSubmonoid.closure ({22, 23} : Set ℕ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have h22 : (22 : ℕ) ∈ AddSubmonoid.closure ({22, 23} : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp)
  have h23 : (23 : ℕ) ∈ AddSubmonoid.closure ({22, 23} : Set ℕ) :=
    AddSubmonoid.subset_closure (by simp)
  have h : (508 : ℕ) = 21 • (22 : ℕ) + 2 • (23 : ℕ) := by norm_num
  rw [h]
  exact add_mem (nsmul_mem h22 21) (nsmul_mem h23 2)

/-- **Equation (37) (`eq:column-gluing`) of `masked_digit_bound.tex`:**
`C = ⟨506, 508, 529⟩ = 23⟨22, 23⟩ + 508 ℕ`. -/
theorem column_gluing :
    {n : ℕ | ∃ x ∈ AddSubmonoid.closure ({22, 23} : Set ℕ), ∃ y : ℕ, n = 23 * x + 508 * y}
      = (AddSubmonoid.closure ({506, 529, 508} : Set ℕ) : Set ℕ) := by
  have h := gluing_eq_closure 23 508 22 23
  norm_num at h
  exact h

/-- The two complete-intersection relation degrees `ars = 11638` and `ab = 11684` of the
column gluing of Section 6 of `masked_digit_bound.tex`, differing by only `46`. -/
theorem column_relation_degrees :
    23 * 22 * 23 = 11638 ∧ 23 * 508 = 11684 ∧ 11684 - 11638 = 46 := by norm_num

/-! ## Frobenius numbers and conductors -/

/-- If a numerical semigroup contains `g` consecutive integers starting at `c`, where `g` is
one of its generators, then it contains every integer `≥ c`.  This is the standard argument
behind the conductor computations of Section 6 of `masked_digit_bound.tex`. -/
theorem mem_closure_of_run {gens : List ℕ} {g c : ℕ} (hg : g ∈ gens) (hg0 : 0 < g)
    (hrun : ∀ i < g, (c + i) ∈ AddSubmonoid.closure {x : ℕ | x ∈ gens}) :
    ∀ n, c ≤ n → n ∈ AddSubmonoid.closure {x : ℕ | x ∈ gens} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hcn
    by_cases h : n < c + g
    · have hi := hrun (n - c) (by omega)
      rwa [show c + (n - c) = n by omega] at hi
    · have hprev := ih (n - g) (by omega) (by omega)
      have hsplit : n = (n - g) + g := by omega
      rw [hsplit]
      exact add_mem hprev (AddSubmonoid.subset_closure hg)

/-- A computable non-membership test for a numerical semigroup. -/
theorem not_mem_closure_of_semiArr {gens : List ℕ} {B i : ℕ} (hiB : i ≤ B)
    (h : (semiArr gens B).getD i false = false) :
    i ∉ AddSubmonoid.closure {x : ℕ | x ∈ gens} := by
  intro hmem
  have := (semiArr_getD_iff_mem gens B i).2 ⟨hiB, hmem⟩
  rw [h] at this
  exact Bool.noConfusion this

/-- A computable membership test for a numerical semigroup. -/
theorem mem_closure_of_semiArr {gens : List ℕ} {B i : ℕ}
    (h : (semiArr gens B).getD i false = true) :
    i ∈ AddSubmonoid.closure {x : ℕ | x ∈ gens} :=
  ((semiArr_getD_iff_mem gens B i).1 h).2

theorem columnSemi_21779 :
    (semiArr columnGeneratorsList 22300).getD 21779 false = false := by native_decide

theorem columnSemi_run :
    ((List.range 506).all fun i =>
      (semiArr columnGeneratorsList 22300).getD (21780 + i) false) = true := by native_decide

/-- **The column Frobenius number of Section 6 of `masked_digit_bound.tex`:** the largest
integer missing from `C = ⟨506, 508, 529⟩` is
`23(22·23 − 22 − 23) + 22·508 = 21779`. -/
theorem column_frobenius :
    23 * (22 * 23 - 22 - 23) + 22 * 508 = 21779 ∧
    (21779 : ℕ) ∉ AddSubmonoid.closure {x : ℕ | x ∈ columnGeneratorsList} ∧
    ∀ n, 21779 < n → n ∈ AddSubmonoid.closure {x : ℕ | x ∈ columnGeneratorsList} := by
  refine ⟨by norm_num, not_mem_closure_of_semiArr (by norm_num) columnSemi_21779, fun n hn => ?_⟩
  refine mem_closure_of_run (g := 506) (c := 21780) (by simp [columnGeneratorsList])
    (by norm_num) (fun i hi => ?_) n (by omega)
  exact mem_closure_of_semiArr (by
    have := List.all_eq_true.1 columnSemi_run i (List.mem_range.2 hi)
    simpa using this)

theorem carryFreeSemi_28921 :
    (semiArr carryFreeGeneratorsList 31000).getD 28921 false = false := by native_decide

theorem carryFreeSemi_run :
    ((List.range 1518).all fun i =>
      (semiArr carryFreeGeneratorsList 31000).getD (28922 + i) false) = true := by native_decide

/-- **The conductor of the six-generator semigroup of Section 6 of
`masked_digit_bound.tex`:** `28921` is missing from `H = ⟨1518, 1524, 1587, 2024, 2032, 2116⟩`
while every integer `≥ 28922` belongs to it, so the conductor is `28922`, substantially larger
than the cutoff `B = 17032`. -/
theorem carryFree_conductor :
    (28921 : ℕ) ∉ AddSubmonoid.closure {x : ℕ | x ∈ carryFreeGeneratorsList} ∧
    (∀ n, 28922 ≤ n → n ∈ AddSubmonoid.closure {x : ℕ | x ∈ carryFreeGeneratorsList}) ∧
    carryFreeB < 28922 := by
  refine ⟨not_mem_closure_of_semiArr (by norm_num) carryFreeSemi_28921, ?_,
    by norm_num [carryFreeB]⟩
  refine mem_closure_of_run (g := 1518) (c := 28922) (by simp [carryFreeGeneratorsList])
    (by norm_num) fun i hi => ?_
  exact mem_closure_of_semiArr (by
    have := List.all_eq_true.1 carryFreeSemi_run i (List.mem_range.2 hi)
    simpa using this)

/-! ## The `2 × 3` generator grid -/

/-- The two row multipliers `{3, 4}` of the generator grid (38) (`eq:grid`) of
`masked_digit_bound.tex`. -/
def gridRows : Finset ℕ := {3, 4}

/-- The three column generators `{506, 508, 529}` of the generator grid (38) (`eq:grid`) of
`masked_digit_bound.tex`. -/
def gridColumns : Finset ℕ := {506, 508, 529}

/-- **Equation (38) (`eq:grid`) of `masked_digit_bound.tex`:**
`{3,4} × {506,508,529} = {1518, 1524, 1587, 2024, 2032, 2116}`, the six generators of the
carry-free mask. -/
theorem grid_eq_carryFreeGenerators :
    Finset.image₂ (· * ·) gridRows gridColumns = carryFreeGenerators := by
  decide

/-- The exact row relation `4(3c) = 3(4c)` of Section 6 of `masked_digit_bound.tex`. -/
theorem grid_row_relation (c : ℕ) : 4 * (3 * c) = 3 * (4 * c) := by ring

/-- The three row-relation degrees `6072, 6096, 6348` of Section 6 of
`masked_digit_bound.tex`, all well below the cutoff `B = 17032`. -/
theorem grid_row_relation_degrees :
    4 * (3 * 506) = 6072 ∧ 4 * (3 * 508) = 6096 ∧ 4 * (3 * 529) = 6348 ∧
      6348 < carryFreeB := by
  norm_num [carryFreeB]

/-- The lift of the column relation `23·506 = 22·529` to the grid, at degree `11638`,
from Section 6 of `masked_digit_bound.tex`. -/
theorem grid_lifted_column_relation :
    5 * 1518 + 2 * 2024 = 11638 ∧ 2 * 1587 + 4 * 2116 = 11638 ∧ 23 * 506 = 22 * 529 := by
  norm_num

/-- The lift of the second gluing relation to the grid, at degree `13800`, from Section 6 of
`masked_digit_bound.tex`. -/
theorem grid_lifted_gluing_relation :
    5 * 1524 + 2 * 2032 + 2116 = 13800 ∧ 7 * 1518 + 2 * 1587 = 13800 := by norm_num

/-- **Equation (39) (`eq:grid-residual`) of `masked_digit_bound.tex`:** for two columns
`c_i < c_j` the grid elements `3c_i + 4c_j` and `4c_i + 3c_j` differ by `c_j − c_i` and have
total cost `7(c_i + c_j)`. -/
theorem grid_residual (ci cj : ℕ) :
    ((3 * ci + 4 * cj : ℕ) : ℤ) - ((4 * ci + 3 * cj : ℕ) : ℤ) = (cj : ℤ) - (ci : ℤ) ∧
      (3 * ci + 4 * cj) + (4 * ci + 3 * cj) = 7 * (ci + cj) := by
  constructor
  · push_cast; ring
  · ring

/-! ## The resulting bounds on the minimum witness cost -/

theorem mem_carryFree_M_iff {n : ℕ} :
    n ∈ carryFreeMaskData.M ↔ n ∈ semiMask carryFreeGeneratorsList carryFreeB := by
  rw [show carryFreeMaskData.M = generatedUpTo carryFreeGenerators carryFreeB from rfl,
    generatedUpTo_eq carryFreeGenerators_coe, List.mem_toFinset]

theorem mem_carryFree_M_3550 : (3550 : ℕ) ∈ carryFreeMaskData.M :=
  mem_carryFree_M_iff.2 (by native_decide)

theorem mem_carryFree_M_3548 : (3548 : ℕ) ∈ carryFreeMaskData.M :=
  mem_carryFree_M_iff.2 (by native_decide)

theorem mem_carryFree_M_3640 : (3640 : ℕ) ∈ carryFreeMaskData.M :=
  mem_carryFree_M_iff.2 (by native_decide)

theorem mem_carryFree_M_3619 : (3619 : ℕ) ∈ carryFreeMaskData.M :=
  mem_carryFree_M_iff.2 (by native_decide)

theorem mem_carryFree_M_3634 : (3634 : ℕ) ∈ carryFreeMaskData.M :=
  mem_carryFree_M_iff.2 (by native_decide)

theorem mem_carryFree_M_3611 : (3611 : ℕ) ∈ carryFreeMaskData.M :=
  mem_carryFree_M_iff.2 (by native_decide)

/-- **`κ(2) ≤ 7098`**, the first of the three explicit bounds of Section 6 of
`masked_digit_bound.tex` coming from the cheap near relation between the columns `506` and
`508`: the witnesses are `3·506 + 4·508 = 3550` and `4·506 + 3·508 = 3548`. -/
theorem carryFree_kappa_two_le : carryFreeMaskData.kappa 2 ≤ 7098 := by
  have h := carryFreeMaskData.kappa_le mem_carryFree_M_3550 mem_carryFree_M_3548
    (by norm_num : ((3550 : ℕ) : ℤ) - ((3548 : ℕ) : ℤ) = 2)
  omega

/-- **`κ(21) ≤ 7259`**, the second of the three explicit bounds of Section 6 of
`masked_digit_bound.tex`, from the columns `508` and `529`: the witnesses are
`3·508 + 4·529 = 3640` and `4·508 + 3·529 = 3619`. -/
theorem carryFree_kappa_twentyone_le : carryFreeMaskData.kappa 21 ≤ 7259 := by
  have h := carryFreeMaskData.kappa_le mem_carryFree_M_3640 mem_carryFree_M_3619
    (by norm_num : ((3640 : ℕ) : ℤ) - ((3619 : ℕ) : ℤ) = 21)
  omega

/-- **`κ(23) ≤ 7245`**, the third of the three explicit bounds of Section 6 of
`masked_digit_bound.tex`, from the columns `506` and `529`: the witnesses are
`3·506 + 4·529 = 3634` and `4·506 + 3·529 = 3611`. -/
theorem carryFree_kappa_twentythree_le : carryFreeMaskData.kappa 23 ≤ 7245 := by
  have h := carryFreeMaskData.kappa_le mem_carryFree_M_3634 mem_carryFree_M_3611
    (by norm_num : ((3634 : ℕ) : ℤ) - ((3611 : ℕ) : ℤ) = 23)
  omega

/-- The column gaps `2`, `21`, `23` include the coprime pair `gcd(2, 21) = 1`, so the cheap
residual directions generate the whole integer lattice, as observed in Section 6 of
`masked_digit_bound.tex`. -/
theorem grid_column_gaps :
    508 - 506 = 2 ∧ 529 - 508 = 21 ∧ 529 - 506 = 23 ∧ Nat.gcd 2 21 = 1 := by norm_num

/-- The contrast drawn in Section 6 of `masked_digit_bound.tex` between the cheap near
relations and the exact value `κ(1) = 14351` (`carryFree_kappa_one`): minimizing `κ(1)` alone
is not an adequate design criterion, because Proposition 2 uses the entire weighted
distribution of `κ(d)`. -/
theorem carryFree_kappa_contrast :
    carryFreeMaskData.kappa 2 ≤ 7098 ∧ carryFreeMaskData.kappa 21 ≤ 7259 ∧
      carryFreeMaskData.kappa 23 ≤ 7245 ∧ carryFreeMaskData.kappa 1 = 14351 :=
  ⟨carryFree_kappa_two_le, carryFree_kappa_twentyone_le, carryFree_kappa_twentythree_le,
    carryFree_kappa_one⟩

end MaskedDigit
