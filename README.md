# A masked-digit lower bound for the Gyarmati–Hennecart–Ruzsa sum–difference constant

This repository contains the proof, certificate data, and independent
verification programs for a new lower bound on the
[Gyarmati–Hennecart–Ruzsa sum–difference constant](https://teorth.github.io/optimizationproblems/constants/3a.html),
denoted $C_{3a}$ in the
[Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems)
repository:

$$
\boxed{C_\{3a\}>1.19102809}.
$$

The construction uses the digit mask

$$
M=\langle1518,1524,1587,2024,2032,2116\rangle\cap[0,17032]
$$

in base 34065. Its six generators form the product grid

$$
\\{3,4\\}\times\\{506,508,529\\}.
$$

The three-column semigroup has the simple-gluing description

$$
\langle506,508,529\rangle
=23\langle22,23\rangle+508\mathbb N_0,
\qquad
508=21\cdot22+2\cdot23.
$$

The proof paper explains how clustered exact relation degrees, cheap
coprime near-relation residuals, and placement of the cutoff before the
conductor help this mask simultaneously suppress its sum partition
polynomial and enlarge its weighted difference partition polynomial.

Please see the proof paper's "Acknowledgements and AI-use disclosure" section to understand how AI has been used in this package.

## Contents

- [`proof/`](proof/) — the mathematical proof in LaTeX and PDF form
- [`certificate/`](certificate/) — the mask, sum support, minimum
  difference costs, metadata, and SHA-256 checksums
- [`verification/`](verification/) — independent verification programs
  in Python, C++/MPFR, and PARI/GP, together with saved run logs

The main manuscript is:

- [`proof/masked_digit_bound.pdf`](proof/masked_digit_bound.pdf)
- [`proof/masked_digit_bound.tex`](proof/masked_digit_bound.tex)

## Verification

Run all commands from the repository root.

### Python

```bash
python3 verification/verify_python.py
```

This reconstructs the mask and certificate data, checks their SHA-256
hashes, computes the conductor from the Apéry set, and independently
evaluates the claimed lower bound using Python's high-precision
`decimal` module.

### C++ with directed MPFR rounding

Install the required packages on Debian or Ubuntu:

```bash
sudo apt install build-essential libmpfr-dev libgmp-dev
```

Compile and run:

```bash
g++ -std=c++17 -O2 -Wall -Wextra -pedantic \
    verification/verify_mpfr.cpp \
    -lmpfr -lgmp \
    -o verification/verify_mpfr

./verification/verify_mpfr
```

The final output should report that the directed-rounding computation
proves

```text
C_3a > 1.19102809
```

The output and build environment from one successful run are recorded in:

- [`verification/verify_mpfr_output.txt`](verification/verify_mpfr_output.txt)
- [`verification/verify_mpfr_environment.txt`](verification/verify_mpfr_environment.txt)

### PARI/GP

With PARI/GP installed, run:

```bash
gp -q verification/verify_gp.gp
```

## Certificate integrity

To check the certificate files against their recorded hashes:

```bash
cd certificate
sha256sum -c SHA256SUMS
```

All entries should report `OK`.

## Building the paper

The committed PDF can be rebuilt with:

```bash
bash proof/build_pdf.sh
```

This requires a LaTeX installation with `latexmk`.

## Reproducibility

The proof uses exact finite certificate data. The numerical conclusion is
checked independently by:

1. a Python reconstruction,
2. a C++ verifier using directed MPFR rounding, and
3. a PARI/GP verifier.

The MPFR verifier is the rigorous floating-point certification of the
stated decimal inequality.

## Author

Logan Kleinwaks

## License

See [`LICENSE`](LICENSE).
