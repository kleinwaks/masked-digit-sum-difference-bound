#!/usr/bin/env python3
"""Turn directed rational pressure bounds into an exact decimal theta bound."""
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

TERMS = 50


def atanh_interval(z):
    z2 = z * z
    power = z
    partial = Fraction(0)
    for j in range(TERMS):
        partial += power / (2 * j + 1)
        power *= z2
    tail = power / ((2 * TERMS + 1) * (1 - z2))
    return partial, partial + tail


def log_integer_interval(n):
    e = n.bit_length() - 1
    p = 1 << e
    z = Fraction(n - p, n + p)
    lo2, hi2 = atanh_interval(Fraction(1, 3))
    loz, hiz = atanh_interval(z)
    return 2 * (e * lo2 + loz), 2 * (e * hi2 + hiz)


def log_rational_interval(n, d):
    nlo, nhi = log_integer_interval(n)
    dlo, dhi = log_integer_interval(d)
    return nlo - dhi, nhi - dlo


def main():
    if len(sys.argv) not in (2, 3, 4):
        raise SystemExit("usage: certify_exponent.py CONSTANTS.json [OUTPUT.json] [DIGITS]")
    source = Path(sys.argv[1])
    output = Path(sys.argv[2]) if len(sys.argv) >= 3 else source.with_name("certified_bound.json")
    digits = int(sys.argv[3]) if len(sys.argv) >= 4 else 8
    c = json.loads(source.read_text())
    scale = int(c["scale"])
    cnum = int(c["difference_lower_num"])
    pnum = int(c["plus_upper_num"])
    q = int(c["q"])
    ratio_lo, _ = log_rational_interval(cnum, pnum)
    _, q_hi = log_integer_interval(q)
    den = 10**digits
    approx = 1 + math.log(cnum / pnum) / math.log(q)
    target = math.floor(approx * den)
    while den * ratio_lo <= (target - den) * q_hi:
        target -= 1
    result = {
        "version": "final-carry-exponent-0.1.0",
        "certified_strict_lower_bound": f"{target / den:.{digits}f}",
        "digits": digits,
        "difference_lower": f"{cnum / scale:.6f}",
        "plus_pressure_root_upper": f"{pnum / scale:.6f}",
        "q": q,
        "plus_depth": int(c["plus_depth"]),
        "sum_pressure_theta_uncertainty_at_most": c["sum_pressure_theta_uncertainty_at_most"],
        "arithmetic": "exact rational atanh enclosures"
    }
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"CERTIFIED theta > {result['certified_strict_lower_bound']}")
    print(f"sum-pressure finite-depth uncertainty <= {result['sum_pressure_theta_uncertainty_at_most']:.12g}")


if __name__ == "__main__":
    main()
