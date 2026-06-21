#!/usr/bin/env python3
"""THE-MACHINE NODE test: continuous energy flux maintains dissipative assembly.

NODE:
    Energy flux must be continuous to maintain the assembled state.

Constraint:
    The assembled state is a maintained throughput state. It appears stable
    only while fuel delivery balances turnover and waste/removal; when flux is
    removed, assembly decays even though the components remain present.
"""

from __future__ import annotations

import numpy as np


def simulate(feed: float, cutoff: int | None, steps: int = 900, dt: float = 0.02) -> dict[str, np.ndarray]:
    fuel = 0.0
    monomer = 1.0
    assembly = 0.0
    waste = 0.0
    fuel_hist = []
    assembly_hist = []
    waste_hist = []
    for t in range(steps):
        current_feed = feed if cutoff is None or t < cutoff else 0.0
        activation = 3.0 * fuel * monomer / (0.18 + fuel)
        disassembly = 0.22 * assembly
        fuel_decay = 0.55 * fuel
        waste_clear = 0.10 * waste
        monomer += dt * (-activation + disassembly)
        assembly += dt * (activation - disassembly)
        fuel += dt * (current_feed - fuel_decay - 0.55 * activation)
        waste += dt * (0.55 * activation + fuel_decay - waste_clear)
        monomer = max(monomer, 0.0)
        assembly = max(assembly, 0.0)
        fuel = max(fuel, 0.0)
        waste = max(waste, 0.0)
        fuel_hist.append(fuel)
        assembly_hist.append(assembly)
        waste_hist.append(waste)
    return {"fuel": np.asarray(fuel_hist), "assembly": np.asarray(assembly_hist), "waste": np.asarray(waste_hist)}


def summarize(feed: float, cutoff: int | None) -> None:
    out = simulate(feed, cutoff)
    a = out["assembly"]
    f = out["fuel"]
    w = out["waste"]
    plateau = float(np.mean(a[-80:]))
    peak = float(np.max(a))
    late_fraction = plateau / max(peak, 1e-12)
    t_peak = int(np.argmax(a))
    print(
        f"feed={feed:.3f} cutoff={str(cutoff):>4s} peak={peak:.4f} t_peak={t_peak:3d} "
        f"late_plateau={plateau:.4f} late/peak={late_fraction:.4f} "
        f"fuel_late={float(np.mean(f[-80:])):.4f} waste_late={float(np.mean(w[-80:])):.4f}"
    )


def main() -> None:
    print("NODE validation: continuous flux maintains dissipative assembly")
    print("feed cutoff peak t_peak late_plateau late/peak fuel_late waste_late")
    for feed in [0.0, 0.04, 0.08, 0.16, 0.32]:
        summarize(feed, cutoff=None)
    print("\nFuel cutoff controls")
    for cutoff in [120, 240, 420]:
        summarize(0.20, cutoff=cutoff)
    print("\nRead: assembly persists at a maintained plateau only with ongoing feed. Fuel cutoff produces a decay tail, so the state is not permanently assembled by component availability alone.")


if __name__ == "__main__":
    main()
