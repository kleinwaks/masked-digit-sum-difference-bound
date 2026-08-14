import RequestProject.OrientedBlocks

/-!
# Why the occurrences of `h` are paired off rather than split into a prefix and a suffix

The proof of Proposition 3 (`prop:controlled-block`) of `masked_digit_bound.tex` prescribes
that, in each residue word, the occurrences of the self-inverse residue `h = q^k/2` be
ordered from left to right and that half of them be oriented as `d(h)` and half as `-d(h)`,
*by a deterministic rule based only on their positions*.  `RequestProject.OrientedBlocks`
realizes that prescription by pairing off consecutive occurrences: the occurrence of
left-to-right index `m` is oriented as `d(h)` when `m` is even and as `-d(h)` when `m` is odd
(`Oriented.osign`).

One might instead take the literal reading "the first half of the occurrences get `d(h)` and
the second half get `-d(h)'' (`Oriented.halfSign` below).  That variant satisfies the
counting requirements just as well — with an even number of occurrences, exactly half carry
each orientation, both orientations have the same residue and the same cost, and their
contributions to the two digit budgets cancel — but it **destroys the injectivity** that the
construction needs: two distinct residue words can then encode the same integer.

`Oriented.halfSign_encoding_not_injective` exhibits such a collision, for the modulus `Q = 4`,
the four residues `{0, 2, 1, 3}` with `h = 2` (which is indeed the nonzero self-inverse
residue modulo `4`), and the two words

* `w  = (h, h, h, h, a)`,
* `w' = (h, h, b, a, 0)`,

both of which contain an even number of occurrences of `h` and both of which encode `106`.

The reason is structural: the prefix/suffix split of the occurrences depends on their *total*
number, hence on the whole word, whereas the pairing rule of `Oriented.osign` depends only on
the prefix of the word up to the position considered.  It is exactly this prefix-determinacy
that lets one read the residue word back off the integer one digit at a time
(`Oriented.oriented_word_injective`).  Both rules are "deterministic rules based only on the
positions of the occurrences", which is all that the source asks for; only the pairing rule
is compatible with the injection into `U - U`.
-/

open scoped BigOperators

namespace MaskedDigit

namespace Oriented

variable {A : Type*} [DecidableEq A]

/-- The literal "first half / second half" orientation: the occurrence of the self-inverse
letter `hh` at position `j` is oriented as `+1` when it lies in the first half of the
occurrences of `hh` in the word, and as `-1` otherwise. -/
def halfSign (hh : A) {l : ℕ} (w : Fin l → A) (j : ℕ) : ℤ :=
  if extend hh w j = hh then
    (if 2 * cnt hh (extend hh w) j < cnt hh (extend hh w) l then 1 else -1)
  else 1

/-- The integer encoded by a word whose blocks are oriented by the prefix/suffix rule
`halfSign`. -/
def halfEnc (Q : ℕ) (hh : A) (val : A → ℤ) {l : ℕ} (w : Fin l → A) : ℤ :=
  ∑ j : Fin l, halfSign hh w (j : ℕ) * val (w j) * (Q : ℤ) ^ (j : ℕ)

/-- The four residues `0, 2, 1, 3` modulo `4`; the letter `1` carries the value `2`, the
nonzero self-inverse residue modulo `4`. -/
def cexVal : Fin 4 → ℤ := ![0, 2, 1, 3]

/-- The word `(h, h, h, h, a)` of the counterexample. -/
def cexW : Fin 5 → Fin 4 := ![1, 1, 1, 1, 2]

/-- The word `(h, h, b, a, 0)` of the counterexample. -/
def cexW' : Fin 5 → Fin 4 := ![1, 1, 3, 2, 0]

/-- **The literal prefix/suffix orientation is not injective.**

For the modulus `Q = 4`, the residue values `cexVal` (which are pairwise distinct modulo `4`)
and the self-inverse letter `hh = 1` (of value `2 = -2` modulo `4`), the two *distinct* words
`cexW` and `cexW'`, each containing an even number of occurrences of `hh`, are encoded by the
same integer once their occurrences of `hh` are oriented by the first-half/second-half rule.

This is why `RequestProject.OrientedBlocks` orients the occurrences of the self-inverse
residue by pairing off consecutive ones (`osign`) instead: that rule is determined by the
prefix of the word, and the encoding it produces *is* injective
(`oriented_word_injective`). -/
theorem halfSign_encoding_not_injective :
    Function.Injective (fun a : Fin 4 => ((cexVal a : ℤ) : ZMod 4)) ∧
      ((cexVal 1 : ℤ) : ZMod 4) = -((cexVal 1 : ℤ) : ZMod 4) ∧
      Even (∑ j, if cexW j = 1 then 1 else 0) ∧
      Even (∑ j, if cexW' j = 1 then 1 else 0) ∧
      cexW ≠ cexW' ∧
      halfEnc 4 (1 : Fin 4) cexVal cexW = halfEnc 4 (1 : Fin 4) cexVal cexW' := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Oriented

end MaskedDigit
