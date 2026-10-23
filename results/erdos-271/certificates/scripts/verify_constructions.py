#!/usr/bin/env python3
"""Reconstruct and verify the public finite certificates used by Paper 2.

This is a reconstruction from the frozen public recipes. It uses
only the Python standard library and performs no network or subprocess calls.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import itertools
import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
V16 = (8, 11, 12, 15)
W16 = (2, 3, 5, 7, 10, 12, 14, 21, 23, 25, 28)
S192 = {
    1, 2, 3, 4, 6, 9, 11, 12, 14, 20, 22, 33, 35, 41, 43, 49, 63, 74, 76,
    82, 88, 94, 96, 102,
}
S768 = {
    1, 2, 3, 4, 5, 8, 9, 12, 13, 16, 21, 24, 33, 36, 41, 44, 45, 48, 53,
    56, 77, 80, 85, 88, 129, 132, 137, 140, 161, 164, 169, 172, 253, 256,
    261, 264, 271, 301, 304, 309, 312, 340, 345, 348, 353, 356, 377, 380,
    385, 388,
}
EXPECTED_HASHES = {
    "a16-set.txt": "03429a757d2ce20b2c3be9016dad53d564bb494100f05316a55422d3c1d793b7",
    "a16-base-window.csv": "820741986eaeeb4d6e931db80f8c4da99c6ce3e3fa650d0ac032995694e7e6c4",
    "a16-cylinder.csv": "7e59db2b5fe2596aa6940df267c2dbf4a878d45b8600ca670dd64ae5245bf26d",
    "a4-base-window.csv": "10e31cd8a6e4fe8ca4f4c9f7217b2d4865e367f2da5dc4e44e39abd15f30aef6",
    "s192-set.txt": "f204b98bbb5528e25160ad2475da67ea9049f161b25d16ceb633b50bdeed07d7",
    "s192-witnesses.csv": "b553f88a0e2df239dab69aaec8b9f0638d79e523613dc0ab9188fe073590bed6",
    "s3072-witnesses.csv": "d89f997c4077382071d1a3a6454db0119af1a2e2e06bedee9b6d2ec4c1184590",
    "s49152-set.txt": "a3a45288c9946ab6c51fab578bc733a49e7cf4d60aa65356b8f2ec95785cc137",
    "s49152-witnesses.csv": "8cd856cd75b4f91c5b4bc13d1f12b05b9c2e1d9e355efc7e9e212cb3c8bcb54b",
    "twenty_two_checks.csv": "961f0917f848d5b2ed72eaa46c3cf0867db4c56ab68850c724a3919b55f6d926",
}


def fail(message: str) -> None:
    raise RuntimeError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def set_bytes(values: set[int]) -> bytes:
    return "".join(f"{x}\n" for x in sorted(values)).encode("utf-8")


def witness_bytes(values: set[int], lo: int, hi: int) -> bytes:
    ordered = sorted(values)
    rows: list[str] = []
    for n in range(lo, hi + 1):
        found: tuple[int, int] | None = None
        for b in ordered:
            if 2 * b <= n:
                continue
            if b >= n:
                break
            a = 2 * b - n
            if a > 0 and a in values:
                found = (a, b)
                break
        if found is None:
            fail(f"uncovered target {n} in [{lo},{hi}]")
        a, b = found
        if not (a in values and b in values and 0 < a < b < n and a + n == 2 * b):
            fail(f"invalid witness for {n}: {(a, b)}")
        rows.append(f"{n},{a},{b}\n")
    return "".join(rows).encode("utf-8")


def digit_family(q: int, digits: tuple[int, ...], leaders: tuple[int, ...], limit: int) -> set[int]:
    answer: set[int] = set()
    tails = [0]
    scale = 1
    while min(leaders) * scale <= limit:
        for leader in leaders:
            for tail in tails:
                value = leader * scale + tail
                if value <= limit:
                    answer.add(value)
        tails = [tail + digit * scale for tail in tails for digit in digits]
        scale *= q
    return answer


def lift(values: set[int]) -> set[int]:
    return {4 * value + digit for value in values for digit in (0, 1)}


def rational_table_bytes() -> bytes:
    output = io.StringIO(newline="")
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(("rank", "leading", "C", "gap_at_zero", "gap_at_two_fifths"))
    target = Fraction(289, 36)
    for rank, leader in enumerate(W16):
        constant = Fraction(14, 3) + rank
        gaps = (
            target * (leader + 1) - constant * constant,
            target * (leader + Fraction(13, 25)) - (constant - Fraction(2, 5)) ** 2,
        )
        if any(gap < 0 for gap in gaps):
            fail(f"negative rational gap at rank {rank}")
        writer.writerow((rank, leader, constant, *gaps))
    return output.getvalue().encode("utf-8")


def generated_files() -> tuple[dict[str, bytes], dict[str, object]]:
    a16 = digit_family(16, V16, W16, 16**4)
    a4 = digit_family(4, (0, 1), (9, 10, 16, 19, 20, 23, 24), 4 * 4737)
    s3072 = (lift(S768) | {1, 2, 3}) - {13}
    s49152 = (lift(lift(s3072) | {1, 2, 3}) | {1, 2, 3}) - {13}

    cylinder_rows: list[str] = []
    cylinder_failures: list[tuple[int, str]] = []
    for rank, leader in enumerate(W16):
        for digits in itertools.product(range(4), repeat=4):
            base4_rank = sum(digit * 4 ** (3 - i) for i, digit in enumerate(digits))
            residue = sum(V16[digit] * 16 ** (3 - i) for i, digit in enumerate(digits))
            n1 = 256 * (11 + 3 * rank) + 3 * (base4_rank + 1)
            n2 = 15 * 65536 * leader + 15 * residue + 8
            lhs = 36 * 15 * 65536 * n1 * n1
            rhs = 289 * 768 * 768 * n2
            digit_word = "".join(str(digit) for digit in digits)
            cylinder_rows.append(f"{rank},{leader},{digit_word},{lhs},{rhs}\n")
            if lhs > rhs:
                cylinder_failures.append((rank, digit_word))
    if cylinder_failures != [(1, "3333")]:
        fail(f"unexpected cylinder failures: {cylinder_failures}")

    files = {
        "a16-set.txt": set_bytes(a16),
        "a16-base-window.csv": witness_bytes(a16, 89, 1446),
        "a16-cylinder.csv": "".join(cylinder_rows).encode("utf-8"),
        "a4-base-window.csv": witness_bytes(a4, 1182, 4737),
        "s192-set.txt": set_bytes(S192),
        "s192-witnesses.csv": witness_bytes(S192, 3, 192),
        "s768-set.txt": set_bytes(S768),
        "s768-witnesses.csv": witness_bytes(S768, 3, 768),
        "s3072-set.txt": set_bytes(s3072),
        "s3072-witnesses.csv": witness_bytes(s3072, 3, 3072),
        "s49152-set.txt": set_bytes(s49152),
        "s49152-witnesses.csv": witness_bytes(s49152, 3, 49152),
        "twenty_two_checks.csv": rational_table_bytes(),
    }
    facts: dict[str, object] = {
        "a16_elements": len(a16),
        "a16_witnesses": 1358,
        "a4_witnesses": 3556,
        "cylinder_rows": len(cylinder_rows),
        "cylinder_expected_failure": {"rank": 1, "leader": 3, "digits": "3333"},
        "static_set_sizes": {"192": len(S192), "768": len(S768), "3072": len(s3072), "49152": len(s49152)},
        "static_witness_counts": {"192": 190, "768": 766, "3072": 3070, "49152": 49150},
    }
    return files, facts


def verify_expected_hashes(files: dict[str, bytes]) -> None:
    for name, expected in EXPECTED_HASHES.items():
        actual = sha256(files[name])
        if actual != expected:
            fail(f"frozen hash mismatch for {name}: {actual} != {expected}")


def extended_checks() -> dict[str, object]:
    limit = 16**5
    recursive = bytearray(limit + 1)
    for value in range(1, limit + 1):
        recursive[value] = value in W16 or (
            value >= 16 and value % 16 in V16 and bool(recursive[value // 16])
        )
    blocks = digit_family(16, V16, W16, limit)
    for value in range(limit + 1):
        if bool(recursive[value]) != (value in blocks):
            fail(f"recursive/block membership mismatch at {value}")
    positive = sorted(blocks)
    count = 0
    for value in range(1, limit + 1):
        if recursive[value]:
            count += 1
        if 36 * (count + 1) ** 2 > 289 * value:
            fail(f"base-16 finite bound fails at {value}")
    uncovered: list[int] = []
    prefix = set(positive)
    for n in range(1, 16**4 + 1):
        if n in prefix:
            continue
        found = False
        for b in positive:
            if 2 * b <= n:
                continue
            if b >= n:
                break
            if 2 * b - n in prefix:
                found = True
                break
        if not found:
            uncovered.append(n)
    if uncovered != [1, 6, 20, 24]:
        fail(f"unexpected uncovered list: {uncovered}")
    return {
        "membership_range": [0, limit],
        "recursion_equals_block_generation": True,
        "finite_uniform_bound_range": [1, limit],
        "uncovered_positive_targets_below_16_pow_4": uncovered,
        "rational_inequalities": 22,
    }


def make_report(files: dict[str, bytes], facts: dict[str, object], extended: dict[str, object] | None) -> dict[str, object]:
    return {
        "schema": "erdos271-certificate-reconstruction-v1",
        "status": "verified-reconstruction",
        "scope": "Finite integer certificates only; no claim of reconstructing the unavailable original package bytes.",
        "canonical_serialization": {
            "sets": "UTF-8 increasing integer plus LF, no header",
            "witnesses": "UTF-8 n,a,b plus LF, increasing n, smallest valid b, no header",
        },
        "facts": facts,
        "files": {
            name: {"bytes": len(data), "sha256": sha256(data)}
            for name, data in sorted(files.items())
        },
        "published_full_hashes_checked": sorted(EXPECTED_HASHES),
        "extended_checks": extended,
        "historical_generator": {
            "path": "original-generator/release_data.py",
            "sha256": "f856393f7b0338ad4b528efc1c697b4e8cd8e7cc0d04868a5aece99c3cbc6469",
            "execution_note": "Archived unchanged for history; do not execute in place because it writes to hard-coded /tmp/rel paths."
        },
        "known_missing_input": {
            "original_verifier": "The exact first-release scripts/verify_constructions.py was not present in the inspected local archives.",
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write deterministic data and verification-report.json")
    parser.add_argument("--extended", action="store_true", help="run bounded checks through 16**5")
    args = parser.parse_args()
    files, facts = generated_files()
    verify_expected_hashes(files)
    extended = extended_checks() if args.extended else None
    if args.write:
        DATA.mkdir(parents=True, exist_ok=True)
        for name, data in files.items():
            target = DATA / name
            if target.exists():
                if target.read_bytes() != data:
                    fail(f"existing certificate differs from reconstruction: {name}")
            else:
                target.write_bytes(data)
    for name, data in files.items():
        target = DATA / name
        if not target.is_file():
            fail(f"missing certificate file: {name}")
        if target.read_bytes() != data:
            fail(f"stored certificate differs from reconstruction: {name}")
    if args.write:
        report = make_report(files, facts, extended)
        (ROOT / "verification-report.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n"
        )
    else:
        for name, expected in sorted(EXPECTED_HASHES.items()):
            print(f"OK {expected}  {name}")
        if args.extended:
            print("OK extended finite checks")


if __name__ == "__main__":
    main()
