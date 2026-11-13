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

## Gates
- [x] M1 Poincaré form, RH ⇔ Poincaré of every Doob chain; bottleneck criterion — compiled
- [x] overlap gluing law; RH ⇔ every conditional coupling contracts; refinement monotonicity — compiled
- [x] binding lower bound from the root block (√ρ/log ρ); RH upper bound — compiled
- [x] archimedean floor `A(0)` without trees; Chebyshev ceiling `2Σ Λ(k)/√k` — compiled
- [ ] two-end lower bound (order √ρ) — written, compile pending
- [ ] floor-tree components at ratio four (dilation process without gap) — compiling
- [ ] bounded margin `gap ≤ μ + c₀`; RH ⇒ Poincaré constant in `[μ, μ + c₀]` — written, compile pending
- [ ] reflection symmetry at infinite block size; shallow-tree selectivity — written, compile pending

## Approach
Folder `formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/`, umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Build on AGZ (`neutralWindow`, `neutralForm`,
`packetForm`, refinement tower, two-well law), HTG inertia and Haynsworth, RHTower Lévy density.

Open threads: margin bounded below ⇒ RH (expected: an off-line zero drives the margin of long
windows to −∞ at rate `ρ^{β−1/2}`; needs a quantitative zero-side test on translates with
vanishing charges); concentration of the ground state on the two ends; parity split of the index
at infinite block size; quantitative overlap law.

## Log
- 2026-11-13 — created; README drafted; modules 1–4 compiled
