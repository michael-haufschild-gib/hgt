#!/usr/bin/env python3
"""Multicore RunPod campaign for literal source-side Laurent matrices."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import traceback
from pathlib import Path

from source_galerkin import compute


def run_job(job: tuple[str, int, int, int, Path, bool]) -> dict[str, object]:
    a, N, digits, grid, out_dir, validate = job
    output = out_dir / f"result-a{a}-N{N}-d{digits}.json"
    try:
        payload = compute(a, N, digits, 1, grid, validate)
        output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        return {
            "a": a,
            "N": N,
            "status": "ok",
            "output": str(output),
            "ground_eigenvalue": payload["ground_eigenvalue"],
            "timings": payload["timings"],
        }
    except Exception:
        return {"a": a, "N": N, "status": "error", "traceback": traceback.format_exc()}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--apertures", nargs="+", default=["0.8", "1.0", "1.2", "1.4", "1.6"])
    parser.add_argument("--ranks", nargs="+", type=int, default=[12, 24, 40, 64, 96])
    parser.add_argument("--digits", type=int, default=120)
    parser.add_argument("--grid", type=int, default=16384)
    parser.add_argument("--workers", type=int, default=min(32, os.cpu_count() or 1))
    parser.add_argument("--out-dir", type=Path, required=True)
    parser.add_argument("--summary", type=Path, required=True)
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    jobs = [
        (a, N, args.digits, args.grid, args.out_dir, N == min(args.ranks))
        for a in args.apertures for N in args.ranks
    ]
    records: list[dict[str, object]] = []
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(run_job, job): job for job in jobs}
        for future in concurrent.futures.as_completed(futures):
            record = future.result()
            records.append(record)
            print(json.dumps(record), flush=True)
    records.sort(key=lambda row: (float(row["a"]), int(row["N"])))
    args.summary.write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    if any(record["status"] != "ok" for record in records):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
