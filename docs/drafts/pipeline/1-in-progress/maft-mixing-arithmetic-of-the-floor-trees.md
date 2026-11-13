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
- [x] two-end lower bound (order √ρ) — compiled
- [x] floor-tree components at ratio four (dilation process without gap) — compiled
- [x] ground state charges both ends: `κ² m² ≤ 4 S_long² bot·top` — compiled
- [x] pole capacity: `μ m + W(φ) ≤ cap·m`; RH ⇒ `μ ≤ √ρ − 1/√ρ + log ρ` — compiled
- [ ] RH ⇒ margin → 0 at infinite block size (three spread copies, plane `A = 0`) — compiling
- [ ] bounded margin `gap ≤ μ + c₀`; RH ⇒ Poincaré constant in `[μ, μ + c₀]` — written, compile pending
- [ ] reflection symmetry at infinite block size; shallow-tree selectivity — written, compile pending

## Approach
Folder `formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/`, umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Build on AGZ (`neutralWindow`, `neutralForm`,
`packetForm`, refinement tower, two-well law), HTG inertia and Haynsworth, RHTower Lévy density,
the zero sum `zetaZeroConfig.W` with `TemperedConfig` and `|γ| ≥ 2`.

Open threads: margin at finite block size (transfer through the tower); margin bounded below ⇒
RH; unconditional leading constant of μ (pole profile `e^{±u/2}` against PNT); shape of the
ground state between the ends; quantitative overlap law.

## Log
- 2026-11-13 — created; README drafted; modules 1–6, 9, 10 compiled; module 11 written
