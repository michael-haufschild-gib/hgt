# Mixing arithmetic of the floor trees (MAFT)

- **ID:** maft
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (programme)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.9
- **Statement:** every Doob chain of a window has spectral gap at least its binding energy (RH); the field studies these chains.

## Goal
Develop the Doob chains of the windows as objects: inertia law, cuts, scale of binding energy and
gap, dilation limit, comparison and curvature methods. B192 itself (one bound state at ratio three
and four) is worked by another agent: do not prove ratio-three/four sign statements here.

## Gates
- [ ] M1 Poincaré form: inertia of `N_W` = slow modes of the Doob chain; one bound state ⇔ gap ≥ μ
- [ ] cut criterion (bottleneck below binding energy ⇒ second bound state)
- [ ] scale law: binding energy ≍ √ρ (lower bound unconditional; RH upper bound 2(ρ−1)/√ρ)
- [ ] dilation limit: translation/reflection invariance of the window form at infinite block size
- [ ] floor-tree components; jets-only mixing rate
- [ ] curvature / Cheeger / canonical-path verdicts calibrated on twisted contacts
- [ ] recursion along doublings (M4)

## Approach
Lean folder `formal/GaloisForLFunctions/MixingArithmeticOfTheFloorTrees/`, umbrella
`MixingArithmeticOfTheFloorTrees.lean`. Build on AGZ (`neutralWindow`, `blockWeight`,
`sum_sum_mul_eq_doob`, `packetForm`), HTG inertia (`hermNegIndex`, `haynsworth_negIndex`),
LST regional log spectrum, SPTL parity sectors.

Scale computation (paper, to formalize): flat-in-log packet `f = x^{−1/2}/√L` on `(1, ρ]` gives
contact energy `−(2/L) Σ_{k≤ρ} Λ(k) k^{−1/2} log(ρ/k) ≈ −8√ρ/L`, archimedean part `O(1)`.
Under RH `N ≥ −2c₀c₁ ≥ −2((ρ−1)/√ρ)‖f‖²`. Middle-cut floor-tree conductance ≈ `4√ρ`.

## Log
- 2026-11-13 — created; README first draft written
