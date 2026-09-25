#!/usr/bin/env python3
"""Independent residual and recomputation checks for selected cached ordinates."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zeros", type=Path, required=True)
    parser.add_argument("--digits", type=int, default=260)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    values: dict[int, str] = {}
    with args.zeros.open(encoding="utf-8") as handle:
        for line in handle:
            if line.startswith("#") or not line.strip():
                continue
            index_text, value = line.split(maxsplit=1)
            values[int(index_text)] = value.strip()

    mp.mp.dps = args.digits
    checks = []
    for index in [1, 400, 1000, 2200]:
        cached = mp.mpf(values[index])
        recomputed = mp.im(mp.zetazero(index))
        residual = abs(mp.zeta(mp.mpf("0.5") + 1j * cached))
        checks.append({
            "index": index,
            "cached": mp.nstr(cached, 60),
            "absolute_recomputation_error": mp.nstr(abs(cached - recomputed), 30),
            "zeta_residual": mp.nstr(residual, 30),
        })
    args.out.write_text(json.dumps({"digits": args.digits, "checks": checks}, indent=2) + "\n",
                        encoding="utf-8")
    print(json.dumps(checks, indent=2))


if __name__ == "__main__":
    main()
