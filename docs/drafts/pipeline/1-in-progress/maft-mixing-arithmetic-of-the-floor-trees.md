# Mixing arithmetic of the floor trees (MAFT)

- **ID:** maft
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.9
- **Statement:** every Doob chain of a window has spectral gap at least its binding energy (RH); the field studies these chains.

## Goal
Develop the Doob chains of the windows as objects: inertia law, cuts, scale of binding energy and
gap, comparison with parts, dilation limit, components of the floor trees. B192 itself (one bound
state at ratio three and four) is worked by another agent: no ratio-three/four sign proofs here.
Results of the form "RH ⇒ X" are calibration only; targets are unconditional statements and
reductions "X ⇒ RH" with X weaker than the known equivalents.

## Gates
- [x] Poincaré form, RH ⇔ Poincaré of every Doob chain; bottleneck criterion
- [x] overlap gluing law; RH ⇔ every conditional coupling contracts; refinement monotonicity
- [x] binding energy of order √ρ (root block, two ends, Chebyshev ceiling, archimedean floor)
- [x] floor-tree components below ratio 9/2 (dilation process without gap)
- [x] ground state charges both ends; pole capacity `μ m + W(φ) ≤ cap·m`
- [x] bounded margin `gap ≤ μ + c₀`; cut law
- [x] reflection at infinite block size; odd sector unbound ⇔ RH
- [x] odd sector bounded below ⇔ RH; rate law of the antisymmetric state
- [x] margin bounded below ⇔ RH, at infinite and at finite block size; windows `(1, 2M]` suffice; Doob form with additive loss
- [x] exponent law for `𝔚`: `θ = ½` unconditionally, `θ < ½` ⇒ zero width `≤ θ`
- [x] margin rate `θ < ½` ⇒ zero width `≤ θ`, at infinite and at finite block size
- [x] dilation process on `(1, Q]` has no gap, for every `Q`
- [x] curvature of the floor trees is exactly zero (`CD(0,∞)`, no `CD(κ,∞)` with `κ > 0`)
- [x] foundational README

## Approach
Folder `formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/`, umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Build on AGZ (`neutralWindow`, `neutralForm`,
`packetForm`, refinement tower, plane of two negative squares), HFP (comb, block averages, limit
to the zeros), SRT and SurfaceOfSpecZ (lag structures, Landau from both sides).

Open: converse of the exponent laws (zero width `θ` ⇒ `𝔚 ≥ −C ρ^{θ+ε}`, margin `≥ −C ρ^{θ+ε}`);
the Doob energy of the jets on the waves at the common returns of `t log k`; the cut of a window
of ratio three; canonical paths and trickle-down for the Doob chains; unconditional leading
constant of μ; quantitative overlap law.

## Log
- 2026-11-13 — created; modules 1–21 compiled and wired
