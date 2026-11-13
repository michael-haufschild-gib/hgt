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
- [x] odd sector bounded below ⇔ RH; rate law of the antisymmetric state (module 14)
- [ ] margin bounded below ⇔ RH at infinite block size (module 15) — compile pending
- [ ] margin of the window matrices bounded below ⇔ RH; windows `(1, 2M]` suffice; Doob form with additive loss (module 16) — compile pending
- [ ] exponent law: `𝔚 ≥ −C√K·mass` unconditionally, `𝔚 ≥ −C K^θ·mass` with `θ < ½` ⇒ zero width `≤ θ` (module 17) — compile pending
- [ ] umbrella wiring of modules 14–17 after their compiles

## Approach
Folder `formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/`, umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Build on AGZ (`neutralWindow`, `neutralForm`,
`packetForm`, refinement tower, plane of two negative squares), HFP (comb, block averages, limit
to the zeros), SRT and SurfaceOfSpecZ (lag structures, Landau from both sides).

Open: converse of the exponent law (zero width `θ` ⇒ `𝔚 ≥ −C ρ^{θ+ε}`); the exponent of the
margin of `N` inside windows of comparable ratio; additive-loss comparison arguments for the
Poincaré inequality; unconditional leading constant of μ; shape of the ground state between the
ends; quantitative overlap law.

## Log
- 2026-11-13 — created; modules 1–17 written
