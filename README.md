# Improved lower bound for the Gyarmati-Hennecart-Ruzsa sum-difference constant using masked digits and controlled carries

This repository contains a proof paper, finite and asymptotic certificates,
and independent verification programs for the Gyarmati-Hennecart-Ruzsa
sum-difference constant (C\_{3a}).

The results are:

```text
explicit finite construction:  C\_3a > 1.19102809
controlled-carry limit:         C\_3a > 1.19519192
```

The distinction matters. The first inequality follows from one explicitly
specified finite set and requires no method-of-types or infinite-block limit.
The second is the stronger limiting result obtained from exact difference and
sum pressures. This presentation follows the certified-value/limit convention
in the Optimization Constants in Mathematics contributing guidelines.

The controlled-carry construction uses

```text
B = 26972
q = 27022
M = <1971,2016,2100,2628,2688,2800> intersect \[0,B]
|M| = 5869
|M+M| = 31274
x = 0x1.ffde827adc0fep-1
```

The rigorous numerical certificate proves

```text
difference pressure root > 582.117820
8192-block sum pressure root < 79.428331
```

and exact rational logarithm enclosures then prove

```text
1 + log(582.117820 / 79.428331) / log(27022) > 1.19519192.
```

The finite construction uses the earlier carry-free mask

```text
Mf = <1518,1524,1587,2024,2032,2116> intersect \[0,17032]
Q = 34065
N = 10^13
xf = 0.9996789017186568
L = 51500691976683641
```

and defines

```text
U = { sum\_(i=0)^(N-1) a\_i Q^i : a\_i in Mf and sum\_i a\_i <= L },
V = 2U.
```

Directed MPFR evaluation of exact finite combinatorial formulas gives

```text
C\_3a > 1.19102809.
```

No element of the enormous set (U) is enumerated; its defining parameters,
type counts, factorial formula, and weighted sumset bound are reconstructed
directly by the verifier.

## Main files

* `proof/masked\_digit\_bound.tex` -- complete proof paper.
* `proof/masked\_digit\_bound.pdf` -- compiled paper.
* `certificate/controlled/` -- final controlled-carry configuration,
positive vector, and certified constants.
* `verification/controlled/` -- rigorous difference/sum pressure verifier and
exact-rational exponent checker.
* `verification/verify\_finite\_mpfr.cpp` -- finite-construction verifier.
* `certificate/` and the original verification programs -- the previous
carry-free certificate, retained for independent reconstruction and for the
finite construction.
* `formalization/lean/` -- the completed Lean 4/Mathlib formalization produced
with Aristotle, including exact certificate data and a one-command verifier.
* `formalization/LEAN\_BLUEPRINT.txt` -- the earlier conceptual blueprint,
retained as historical and explanatory material rather than as a proof.
* `pr/` -- proposed optimizationproblems edits and pull-request text.

The proof paper includes an AI-use disclosure describing how language models
were used. The author directed the research and computation, ran the software,
reviewed the claims, and takes responsibility for the submission.

## Quick finite verification

On Debian or Ubuntu:

```bash
sudo apt install build-essential libmpfr-dev libgmp-dev

g++ -std=c++17 -O2 -Wall -Wextra -Wpedantic \\
  verification/verify\_finite\_mpfr.cpp \\
  -lmpfr -lgmp -o verification/verify\_finite\_mpfr

./verification/verify\_finite\_mpfr
```

This check normally completes in seconds. It reconstructs the mask, all
minimum difference costs, the complete symmetric type, and the rigorous
finite logarithm bounds. Its final line should be:

```text
PASS: the explicit finite set V=2U proves C\_3a > 1.19102809
```

## Full controlled-carry verification

The controlled certificate is much more computationally demanding. The verifier
below repeats only the final certificate, not the search.

```bash
g++ -std=c++17 -O3 -Wall -Wextra -Wpedantic \\
  -fopenmp -fno-fast-math -ffp-contract=off \\
  verification/controlled/certify\_candidate.cpp \\
  -o verification/controlled/certify\_candidate

OMP\_NUM\_THREADS=20 verification/controlled/certify\_candidate \\
  certificate/controlled/candidate.cfg \\
  certificate/controlled/pf8\_vector.hex \\
  certificate/controlled/rigorous\_constants.recomputed.json \\
  20

python3 verification/controlled/verify\_exponent.py \\
  certificate/controlled/rigorous\_constants.recomputed.json \\
  certificate/controlled/certified\_bound.recomputed.json 8
```

The generated files should report

```text
difference\_lower = 582.117820
plus\_pressure\_root\_upper = 79.428331
certified\_strict\_lower\_bound = 1.19519192
```

Do not compile the controlled verifier with `-ffast-math`. It requires
IEEE-754 binary64, round-to-nearest operation, and no excess-precision
evaluation.

## Rechecking the shipped exponent only

The pressure computation does not need to be repeated merely to check the
final decimal conversion:

```bash
python3 verification/controlled/verify\_exponent.py \\
  certificate/controlled/rigorous\_constants.json \\
  /tmp/certified\_bound.json 8
```

This script uses exact rational arithmetic and explicit atanh-series tails;
it does not trust a floating-point implementation of `log`.

## Previous carry-free cross-checks

The original carry-free package remains available:

```bash
python3 verification/verify\_python.py

g++ -std=c++17 -O2 -Wall -Wextra -Wpedantic \\
  verification/verify\_mpfr.cpp -lmpfr -lgmp \\
  -o verification/verify\_mpfr
./verification/verify\_mpfr

gp -q verification/verify\_gp.gp
```

## Building the paper

```bash
bash proof/build\_pdf.sh
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

The formal theorem `MaskedDigit.MaskData.controlled\_block\_bound` is the full
finite-block statement from the paper. The formal proof uses product-weight
concentration with an even-parity restriction, while the paper presents a
fixed-exact-type argument; both prove the same inequality. The large exact
certificate checks use `native\_decide`, so the final numerical theorems'
axiom reports include `Lean.trustCompiler`.

## Author

Logan Kleinwaks

## License

See `LICENSE`.

