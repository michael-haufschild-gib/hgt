# Fredholm Index Realization and Structural Homotopy of the Glued Weil State

- **ID:** sc-glued-weil-fredholm-index-homotopy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-3110/obstacles-summary.md §2.6.2 · docs/reports/review-3110/route-obstacles.md §SC
- **Statement:** Determine and prove unconditionally whether `κ(φ_c) − 1` is the Fredholm index of an operator `D_ζ` built from integers and adeles, connected through Fredholm operators to an operator of index `0` along a path whose symbol stays invertible for a structural reason, together with all unconditional implications.

## Goal
Resolve Question 2.6.2 of `obstacles-summary.md` unconditionally in Lean 4 without estimates, mere reformulation criteria, or toy-class no-gos, addressing both AKG's purely additive zero counter and the existence/obstruction of symbol-invertible Fredholm homotopies of `D_ζ`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems in dedicated subfolder, `lake --old env lean` clean, `#print axioms` PASS

## Approach
1. Construct source-pure Wiener–Hopf / Toeplitz operators on `L²(ℝ)` from integer theta / tangent-disc Blaschke / boost-hyperplane data and test whether their Fredholm index realizes `κ(φ_c^{(t)}) − 1` and `κ(φ_c) − 1`.
2. Interrogate structural mechanisms for symbol invertibility along continuous deformations to an index-`0` model (sectoriality, heat deformation, boost-shell decomposition, Cayley/Krein transforms, two-prime rigidity).

## Log
- 2026-10-31 — created in 1-in-progress
