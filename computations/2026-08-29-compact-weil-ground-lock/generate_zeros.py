#!/usr/bin/env python3
"""Generate a reusable high-precision table of low zeta ordinates on RunPod."""

from __future__ import annotations

import argparse
import multiprocessing as mp_pool
from pathlib import Path


def one_zero(task: tuple[int, int]) -> tuple[int, str]:
    index, digits = task
    import mpmath as mp

    mp.mp.dps = digits + 15
    ordinate = mp.im(mp.zetazero(index))
    return index, mp.nstr(ordinate, digits)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--count", type=int, required=True)
    parser.add_argument("--digits", type=int, required=True)
    parser.add_argument("--workers", type=int, default=64)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    tasks = [(index, args.digits) for index in range(1, args.count + 1)]
    context = mp_pool.get_context("spawn")
    with context.Pool(processes=args.workers, maxtasksperchild=20) as pool:
        rows = list(pool.imap_unordered(one_zero, tasks, chunksize=1))
    rows.sort()

    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", encoding="utf-8") as handle:
        handle.write(f"# mpmath zetazero; count={args.count}; digits={args.digits}\n")
        for index, ordinate in rows:
            handle.write(f"{index}\t{ordinate}\n")


if __name__ == "__main__":
    main()
