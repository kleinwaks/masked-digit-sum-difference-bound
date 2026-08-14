# Improved lower bound for the Gyarmati-Hennecart-Ruzsa sum-difference constant using masked digits and controlled carries

This repository contains a Lean-formalized proof paper, finite and asymptotic certificates,
and independent verification programs for the [Gyarmati-Hennecart-Ruzsa
sum-difference constant](https://teorth.github.io/optimizationproblems/constants/3a.html), denoted $C\_{3a}$ in the [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems)
repository.

The results are:

$$C\_{3a} > 1.19519192$$

in the controlled-carry limit and

$$C\_{3a} > 1.19102809$$

in the finite construction.

The first is the stronger limiting result obtained from exact difference and sum pressures. The second follows from one explicitly specified finite (but very large) set and requires no method-of-types or infinite-block limit. This presentation follows the certified-value/limit convention in the Optimization Constants in Mathematics contributing guidelines.

The controlled-carry construction uses the semigroup-based digit mask $\langle1971,2016,2100,2628,2688,2800\rangle\cap[0,26972]$ in base $27022$.

The finite construction uses the earlier carry-free mask $\langle1518,1524,1587,2024,2032,2116\rangle\cap[0,17032]$ in base $34065$ with up to $10^{13}$ digits. Because of the large size of this finite construction, the verifier uses bounds on sumset and difference set cardinalities, rather than exact enumeration, as described in the proof paper.

The proof paper explains the properties of these semigroup-based masks that lead to large lower bounds on $C\_{3a}$, though it is not known whether this type of construction is optimal.

Similar constructions with more than six generators have been explored, but have not yet yielded an improvement.

Please see the proof paper's "Formal verification and AI-use disclosure" section to understand how formal verification and AI have been used in this package. 

## Main Contents

- [`proof/`](proof/) — the mathematical proof in LaTeX and PDF form
- [`formalization/lean/`](formalization/lean/) — the completed Lean 4/Mathlib formalization produced with Aristotle (Harmonic), including exact certificate data and a one-command verifier
- [`formalization/LEAN_BLUEPRINT.txt`](formalization/LEAN_BLUEPRINT.txt) — a conceptual blueprint provided to Aristotle to help guide the formalization, retained as historical and explanatory material rather than as a proof
- [`certificate/controlled/`](certificate/) — final controlled-carry configuration, positive vector, and certified constants
- [`certificate/`](certificate/) — the previous carry-free certificate, retained for independent reconstruction and for the finite construction
- [`verification/controlled/`](verification/controlled/) — rigorous difference/sum pressure verifier and exact-rational exponent checker
- [`verification/verify_finite_mpfr.cpp`](verification/verify_finite_mpfr.cpp) — finite-construction verifier

## Quick finite verification

On Debian or Ubuntu:

```bash
sudo apt install build-essential libmpfr-dev libgmp-dev

g++ -std=c++17 -O2 -Wall -Wextra -Wpedantic \\
  verification/verify_finite_mpfr.cpp \\
  -lmpfr -lgmp -o verification/verify_finite_mpfr

./verification/verify_finite_mpfr
```

This check normally completes in seconds. It reconstructs the mask, all
minimum difference costs, the complete symmetric type, and the rigorous
finite logarithm bounds. Its final line should be:

```text
PASS: the explicit finite set V=2U proves C_3a > 1.19102809
```

## Full controlled-carry verification

The controlled certificate is much more computationally demanding. The verifier
below repeats only the final certificate, not the search.

```bash
g++ -std=c++17 -O3 -Wall -Wextra -Wpedantic \\
  -fopenmp -fno-fast-math -ffp-contract=off \\
  verification/controlled/certify_candidate.cpp \\
  -o verification/controlled/certify_candidate

OMP_NUM_THREADS=20 verification/controlled/certify_candidate \\
  certificate/controlled/candidate.cfg \\
  certificate/controlled/pf8_vector.hex \\
  certificate/controlled/rigorous_constants.recomputed.json \\
  20

python3 verification/controlled/verify_exponent.py \\
  certificate/controlled/rigorous_constants.recomputed.json \\
  certificate/controlled/certified_bound.recomputed.json 8
```

The generated files should report

```text
difference_lower = 582.117820
plus_pressure_root_upper = 79.428331
certified_strict_lower_bound = 1.19519192
```

Do not compile the controlled verifier with `-ffast-math`. It requires
IEEE-754 binary64, round-to-nearest operation, and no excess-precision
evaluation.

## Rechecking the shipped exponent only

The pressure computation does not need to be repeated merely to check the
final decimal conversion:

```bash
python3 verification/controlled/verify_exponent.py \\
  certificate/controlled/rigorous_constants.json \\
  /tmp/certified_bound.json 8
```

This script uses exact rational arithmetic and explicit atanh-series tails;
it does not trust a floating-point implementation of `log`.

## Previous carry-free cross-checks

The original carry-free package remains available with verified in written in Python, C++/MPFR, and PARI/GP:

```bash
python3 verification/verify_python.py

g++ -std=c++17 -O2 -Wall -Wextra -Wpedantic \\
  verification/verify_mpfr.cpp -lmpfr -lgmp \\
  -o verification/verify_mpfr
./verification/verify_mpfr

gp -q verification/verify_gp.gp
```

## Building the paper

```bash
bash proof/build_pdf.sh
```

This requires `latexmk` and the LaTeX packages named in the source.

## Verifying the Lean formalization

The Lean project is pinned to Lean 4.28.0 and a fixed Mathlib revision. On a
machine with `elan`, `git`, `curl`, and `zstd` installed, run:

```bash
cd formalization/lean
./verify.sh
```

The first run downloads the pinned toolchain, Mathlib dependencies, and the
Mathlib build cache. It can therefore take several minutes and use substantial
disk space. A successful run ends with `PASS` after building the complete
project, printing the principal theorem and axiom reports, and checking that
the project sources contain no `sorry`, `admit`, or explicit project axiom.

The formal theorem `MaskedDigit.MaskData.controlled_block_bound` is the full
finite-block statement from the paper. The formal proof uses product-weight
concentration with an even-parity restriction, while the paper presents a
fixed-exact-type argument; both prove the same inequality. The large exact
certificate checks use `native_decide`, so the final numerical theorems'
axiom reports include `Lean.trustCompiler`.

## Author

Logan Kleinwaks

## License

See [`LICENSE`](LICENSE).

