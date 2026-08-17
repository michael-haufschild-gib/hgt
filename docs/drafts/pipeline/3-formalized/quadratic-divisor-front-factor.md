# Quadratic divisor-front factor

- **ID:** quadratic-divisor-front-factor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ca_bulk_edge_manuscript_revised.pdf`, §9, equation (52)
- **Statement:** In `ℚ⟦X⟧`, the exact quadratic local correction `q = X²(1-X)/(1-X²)` satisfies `(1-X²)(1+q)=1-X³` and has coefficients `q₂=1`, `q₃=-1`, `q₄=1`.

## Goal

Give future divisor-front work a denominator-free, hypothesis-free formal-series interface for the
first nontrivial local layer. This deliberately formalizes only the exact algebraic input to the
paper's asymptotic expansion, not its RH-conditional or analytic claims.

## Gates

- [x] 0 → 1 in-progress: source-pure exact residue, routine proof, no RH or numerical input
- [x] 1 → 2 fully-proven: complete proof below; dependencies are formal power-series geometric
  inversion and coefficient convolution
- [x] 2 → 3 formalized: Lean theorem `quadraticLayerCorrection_initial_jet` in
  `formal/GaloisForLFunctions/RHTower/QuadraticDivisorFrontFactor.lean`; source check and targeted
  build green; axiom audit is only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4 publication-ready: not a publication claim; `[REDISCOVERED]` algebraic bridge

## Paper proof

Let `G = 1 + X² + X⁴ + ⋯`; formally, `(1-X²)G=1`. Define
`q = X²(1-X)G`. Then

`(1-X²)(1+q) = 1-X² + X²(1-X)((1-X²)G) = 1-X³`.

The first coefficients of `G` are `G₀=1`, `G₁=0`, `G₂=1`; convolution gives
`q₂=G₀=1`, `q₃=-G₀+G₁=-1`, and `q₄=G₂-G₁=1`. This is exact in `ℚ⟦X⟧` and has no hypotheses.

## Audit

- **Internal:** no existing superior/colossally-abundant or Lambert-`W` layer interface. The
  available Lambert series are different transforms.
- **External:** `[REDISCOVERED]`; finite geometric-series algebra, not new scientific knowledge.
- **Open core for full §9:** coefficient control for `log(1+q)` after formal substitution, then
  analytic realization. This card does not claim either step.

## Log

- 2026-08-17 — created in 1-in-progress; exact residue isolated from the manuscript.
- 2026-08-17 — formalized as `quadraticLayerEvenGeom_mul_denominator`,
  `quadraticLayerFrontFactor`, and `quadraticLayerCorrection_initial_jet`; wired into RHTower.
