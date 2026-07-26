#!/usr/bin/env python3
"""Independent exact reconstruction and high-precision cross-check.

This verifier uses only the Python standard library.  It reconstructs the
semigroup mask and every shipped certificate file from the six generators.
It is not the rigorous floating-point certificate; verify_mpfr.cpp supplies
directed rounding.
"""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
from decimal import Decimal, localcontext
from pathlib import Path

B = 17032
Q = 34065
GENERATORS = (1518, 1524, 1587, 2024, 2032, 2116)
LAMBDA = Decimal(
    "0.000321149844434550835903084464712287774157626054669874186964"
)
TARGET = Decimal("1.19102809")
EXPECTED = {
    "mask_size": 3121,
    "sum_size": 18730,
    "diff_size": 32369,
    "difference_cover": 13066,
    "conductor": 28922,
    "kappa_1": 14351,
}


def semigroup_members(limit: int) -> bytearray:
    reachable = bytearray(limit + 1)
    reachable[0] = 1
    for n in range(limit + 1):
        if not reachable[n]:
            continue
        for g in GENERATORS:
            if n + g <= limit:
                reachable[n + g] = 1
    return reachable


def apery_conductor() -> int:
    """Compute the conductor from the Apéry set modulo the multiplicity."""

    multiplicity = min(GENERATORS)
    inf = 10**30
    dist = [inf] * multiplicity
    dist[0] = 0
    queue: list[tuple[int, int]] = [(0, 0)]
    while queue:
        value, residue = heapq.heappop(queue)
        if value != dist[residue]:
            continue
        for g in GENERATORS:
            new_value = value + g
            new_residue = new_value % multiplicity
            if new_value < dist[new_residue]:
                dist[new_residue] = new_value
                heapq.heappush(queue, (new_value, new_residue))
    if any(value == inf for value in dist):
        raise RuntimeError("generators do not define a numerical semigroup")
    return max(dist) - multiplicity + 1


def reconstruct() -> tuple[list[int], list[int], list[tuple[int, int]], int, int]:
    reachable = semigroup_members(B)

    mask = [n for n in range(B + 1) if reachable[n]]
    sums = sorted({a + b for a in mask for b in mask})

    inf = 10**30
    costs = [inf] * (2 * B + 1)
    for a in mask:
        for b in mask:
            idx = a - b + B
            c = a + b
            if c < costs[idx]:
                costs[idx] = c
    diff_costs = [(idx - B, c) for idx, c in enumerate(costs) if c < inf]

    cost_dict = dict(diff_costs)
    difference_cover = 0
    while difference_cover + 1 in cost_dict:
        difference_cover += 1

    return mask, sums, diff_costs, difference_cover, apery_conductor()


def exact_checks(
    mask: list[int],
    sums: list[int],
    diff_costs: list[tuple[int, int]],
    difference_cover: int,
    conductor: int,
) -> None:
    cost_dict = dict(diff_costs)
    checks = {
        "mask_size": len(mask),
        "sum_size": len(sums),
        "diff_size": len(diff_costs),
        "difference_cover": difference_cover,
        "conductor": conductor,
        "kappa_1": cost_dict[1],
    }
    if mask[0] != 0 or mask[-1] != B:
        raise AssertionError("wrong mask endpoints")
    for key, expected in EXPECTED.items():
        if checks[key] != expected:
            raise AssertionError(f"{key}: got {checks[key]}, expected {expected}")


def numerical_check(
    sums: list[int], diff_costs: list[tuple[int, int]]
) -> tuple[Decimal, Decimal, Decimal, Decimal]:
    with localcontext() as ctx:
        ctx.prec = 110
        pplus = sum(
            ((-LAMBDA * Decimal(s)).exp() for s in sums), start=Decimal(0)
        )
        pminus = sum(
            ((-LAMBDA * Decimal(c)).exp() for _, c in diff_costs),
            start=Decimal(0),
        )
        f_value = (pminus / pplus).ln()
        th = Decimal(1) + f_value / Decimal(Q).ln()
    if th <= TARGET:
        raise AssertionError(f"theta={th} does not exceed {TARGET}")
    return pminus, pplus, f_value, th


def certificate_text(
    mask: list[int],
    sums: list[int],
    diff_costs: list[tuple[int, int]],
    difference_cover: int,
    conductor: int,
) -> dict[str, str]:
    metadata = {
        "B": B,
        "base": Q,
        "generators": list(GENERATORS),
        "mask_size": len(mask),
        "sum_size": len(sums),
        "diff_size": len(diff_costs),
        "difference_cover": difference_cover,
        "conductor": conductor,
        "kappa_1": dict(diff_costs)[1],
        "lambda_decimal": str(LAMBDA),
        "certified_theta": str(TARGET),
    }
    return {
        "metadata.json": json.dumps(metadata, indent=2, sort_keys=True) + "\n",
        "mask.txt": "".join(f"{n}\n" for n in mask),
        "sum_support.txt": "".join(f"{n}\n" for n in sums),
        "difference_costs.tsv": "d\tkappa\n" + "".join(f"{d}\t{c}\n" for d, c in diff_costs),
    }


def write_certificate(directory: Path, files: dict[str, str]) -> None:
    directory.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (directory / name).write_text(text, encoding="utf-8")
    hashes = []
    for name in sorted(files):
        digest = hashlib.sha256((directory / name).read_bytes()).hexdigest()
        hashes.append(f"{digest}  {name}\n")
    (directory / "SHA256SUMS").write_text("".join(hashes), encoding="utf-8")


def check_certificate(directory: Path, files: dict[str, str]) -> None:
    for name, expected in files.items():
        path = directory / name
        if not path.is_file():
            raise FileNotFoundError(path)
        actual = path.read_text(encoding="utf-8")
        if actual != expected:
            raise AssertionError(f"certificate mismatch: {name}")

    hash_path = directory / "SHA256SUMS"
    if not hash_path.is_file():
        raise FileNotFoundError(hash_path)
    for line in hash_path.read_text(encoding="utf-8").splitlines():
        digest, name = line.split("  ", 1)
        actual_digest = hashlib.sha256((directory / name).read_bytes()).hexdigest()
        if actual_digest != digest:
            raise AssertionError(f"SHA-256 mismatch: {name}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--certificate-dir",
        type=Path,
        default=Path(__file__).resolve().parents[1] / "certificate",
    )
    parser.add_argument("--write-certificate", action="store_true")
    args = parser.parse_args()

    mask, sums, diff_costs, difference_cover, conductor = reconstruct()
    exact_checks(mask, sums, diff_costs, difference_cover, conductor)
    pminus, pplus, f_value, th = numerical_check(sums, diff_costs)
    files = certificate_text(
        mask, sums, diff_costs, difference_cover, conductor
    )

    if args.write_certificate:
        write_certificate(args.certificate_dir, files)
    else:
        check_certificate(args.certificate_dir, files)

    print("Exact combinatorial reconstruction: PASS")
    print(
        f"B={B} base={Q} |M|={len(mask)} |M+M|={len(sums)} "
        f"|M-M|={len(diff_costs)} cover={difference_cover} "
        f"conductor={conductor} kappa(1)={dict(diff_costs)[1]}"
    )
    print(f"Pminus = {pminus}")
    print(f"Pplus  = {pplus}")
    print(f"F      = {f_value}")
    print(f"theta  = {th}")
    print("PASS: Python reconstruction and certificate hashes agree")


if __name__ == "__main__":
    main()
