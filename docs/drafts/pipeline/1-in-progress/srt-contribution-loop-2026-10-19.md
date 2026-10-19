# SRT contribution loop (goal: 100 field-native contributions)

- **ID:** srt-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/SquareRootThreshold/README.md (read-only)
- **Statement:** Develop the Square-Root Threshold field by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field.

## Goal
100 significant contributions: native to SRT (its objects: configurations, apertures, heights,
windows, depth, lattices, prime polynomial), expanding what the field explains or solves.

## Contribution ledger
| # | Module | Theorem(s) | Content |
|---|---|---|---|

## Conjecture queue
1. **Run (block) visibility law.** A run of `N` consecutive lattice zeros pushed to depth `δ`
   inside the doubled on-line lattice of spacing `2π/L`: invisible for `cosh(2δa) ≤ 2`, uniformly
   in `N` and `L ≥ 4a`; visible for `cosh(δa) > 1 + 16π` once `L` and `N` are large. Edges carry
   the visibility (kernel `cot(πu/L) ≈ L/(πu)`). Contrast: one pair hides to `log(4δL)/2δ`,
   the infinite lattice to `L/2`.
2. Periodic depth profiles: exact Poisson formula with symbol
   `D(m) = Σ_r 2cosh(δ_r mL/P) e^{2πirm/P}`; Toeplitz visibility law.
3. Sparse off-line sublattice (density `1/P`): discrete isolated-pair law below `L/2`.
4. Smooth depth ramps: visibility aperture grows with ramp length (roughness law).

## Log
- 2026-10-19 — loop started; README and review read; queue seeded.
