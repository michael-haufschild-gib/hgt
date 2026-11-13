# Review-1311 A19, A20: explicit heat-horizon height; Jensen rung at the saddle scale

- **ID:** r1311-a19-a20
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), per task
- **Source:** `docs/reports/review-1311/route-obstacles.md` S4 (A19, A20)
- **Statement:** A20: RH through `T` gives real-rootedness of `R_d(Ξ)` for `d ≤ 4T²+1`. A19: a closed-form `X₀(ε)` for the Weyl heat horizon `3/2+ε`.

## Status
| # | Task | Status | Lean |
|---|---|---|---|
| A20 | Jensen rung past `d⁴ ≪ T log T` | paper proof below; Lean in progress | `FiniteFreeProbability/JensenSectorTheorem.lean`, `VerifiedHeightRungs/TheJensenRungAtTheSaddleScale.lean` |
| A19 | explicit height of the heat horizon | open | |

## A20 — paper proof

`R_d(f) = f(D)X^d`. Dictionary: `R_d(fg) = R_d(f) ⊞_d R_d(g)` (`jensenRev_mul`); Walsh: `⊞_d` of real-rooted
polynomials of degree `d` is real-rooted (`splits_ffConv`). So the real symbols `h` with `h(0) ≠ 0` and
`h(D)X^d` real-rooted are closed under products: each real irreducible factor is tested alone.

- Linear factor `c + bw`: `h(D)X^d = X^{d−1}(cX + bd)`.
- Quadratic factor `c + bw + aw²`: `h(D)X^d = X^{d−2}(cX² + bdX + ad(d−1))`, discriminant
  `d(db² − 4ac(d−1))`. With roots `ρ, ρ̄`, `ρ = γ + iδ`: `b/a = −2γ`, `c/a = γ² + δ²`, so the
  discriminant is `≥ 0` iff `(d−1)δ² ≤ γ²`.

**Sector theorem.** A real polynomial symbol `h`, `h(0) ≠ 0`, all of whose complex roots lie in the double
sector `(d−1)(Im ρ)² ≤ (Re ρ)²` has `h(D)X^d` real-rooted. The sector is exact for one conjugate pair
(`d ≥ 2`).

**Rung.** The Hadamard approximants of `Ξ` are real polynomials whose roots are spectral points
`γ + iδ` of zeros, `|δ| < ½`. Under RH through `T`: `|γ| ≤ T ⇒ δ = 0`; `|γ| > T ⇒ (d−1)δ² < (d−1)/4 ≤ T² < γ²`
when `d ≤ 4T² + 1`. The sector theorem and the coefficient limit give `N_d = 0`.

The pair criterion is the Jensen form of de Bruijn's bound: the root near `x = d/γ` sees heat time
`γ²/(2d)`, and `γ²/(2d) ≥ δ²/2` is the sector.

## Log
- 2026-11-13 — created; A20 mechanism found (Walsh closure makes the pair test independent).
