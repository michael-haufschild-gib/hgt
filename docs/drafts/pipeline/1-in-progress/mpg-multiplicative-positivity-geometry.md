# Multiplicative Positivity Geometry: foundations

- **ID:** mpg-foundations
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2510/hard-obstacles-summary.md §4 (arithmetic forcing theory / multiplicative positivity geometry)
- **Statement:** Positivity of Euler log-coefficients is positive-definiteness of the boundary divisor on the Bohr dual of ℝ; this classifies, realizes and sharply bounds every boundary-line forcing law, and fixes the exact constants of interior forcing with growth input.

## Goal
Build the programme `formal/GaloisForLFunctions/MultiplicativePositivityGeometry/` with umbrella and README. Pillars:

1. Positive-definite functions on additive groups: `|φ| ≤ φ 0`, translation law at `|φ h| = φ 0`, integer-valued classification `φ = χ·1_H`, Fejér progression bound.
2. Boundary positivity: cosine traces with nonnegative weights are positive definite; boundary divisors (limits of `x·trace`) are positive definite.
3. Simple-pole classification on the real line: `D = δ₀`, `1_{cℤ}`, or alternating on `cℤ` (discrete support).
4. Sharp progression law: total zero mass along a pole-free progression ≤ `D(0)/2`.
5. Realization: ζ-twists by nonnegative cosine polynomials realize every finitely supported PD profile; one-prime geometric models realize the infinite types.
6. Exact Fejér barrier `a₁ ≤ 2cos(π/(K+2))·a₀`, attained.
7. Growth-to-forcing law: certified width exactly `(√κ − 1)²/M`.
8. ζ: boundary divisor = δ₀ from positive-definiteness; boundary completeness and minimality of the invariants.

Non-circularity: every ζ input is `Λ ≥ 0`, the residue at 1 and analytic factorization; no zero-free input.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized: each pillar checked with `lake --old env lean`

## Approach
Real-coefficient Gram forms; three-point Gram vectors `(s, ∓s, t)` for translation laws; Fejér constant vectors on progressions; roots-of-unity quadrature for the exact barrier; limits of closed PD cones.

## Log
- 2026-10-25 — created in 1-in-progress
