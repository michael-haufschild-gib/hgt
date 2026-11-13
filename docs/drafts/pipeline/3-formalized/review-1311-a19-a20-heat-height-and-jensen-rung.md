# Review-1311 A19, A20: explicit heat-horizon height; Jensen rung at the saddle scale

- **ID:** r1311-a19-a20
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), per task
- **Source:** `docs/reports/review-1311/route-obstacles.md` S4 (A19, A20)
- **Statement:** A20: RH through `T` gives real-rootedness of `R_d(Ξ)` for `d ≤ 4T²+1`, and `4T²+1` is sharp for zero configurations. A19: the Weyl heat horizon `3/2+ε` holds above the height `exp(10²⁰/ε⁴)`.

## Status
| # | Task | Status | Lean |
|---|---|---|---|
| A20 | Jensen rung past `d⁴ ≪ T log T` | formalized | `FiniteFreeProbability/JensenSectorTheorem.lean`: `splits_diffOp_X_pow_of_sector`, `splits_diffOp_pairSymbol_iff`; `VerifiedHeightRungs/TheJensenRungAtTheSaddleScale.lean`: `jensenNonrealCount_eq_zero_of_sector`, `jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width`, `jensenNonrealCount_eq_zero_of_rhVerifiedThrough_sq`, `jensenNonrealCount_eq_zero_of_le` (`d ≤ 17957`), `exists_pair_beyond_rung` |
| A19 | explicit height of the heat horizon | formalized (card `explicit-weyl-heat-height`) | `ZeroConfigurationGeometry/HeatScaleRepulsion/TheExplicitHeightOfTheWeylHorizon.lean`: `riemannHeat_zeros_real_simple_weyl_explicit`, `riemannHeat_zeros_real_simple_weyl_explicit_of_pos` |

## A20 — paper proof

`R_d(f) = f(D)X^d`. Dictionary: `R_d(fg) = R_d(f) ⊞_d R_d(g)` (`jensenRev_mul`); Walsh: `⊞_d` of real-rooted
polynomials of degree `d` is real-rooted (`splits_ffConv`). So the real symbols `h` with `h(0) ≠ 0` and
`h(D)X^d` real-rooted are closed under products: each real irreducible factor is tested alone.

- Linear factor `c + bw`: `h(D)X^d = X^{d−1}(cX + bd)`.
- Quadratic factor `c + bw + aw²`: `h(D)X^d = X^{d−2}(cX² + bdX + ad(d−1))`, discriminant
  `d(db² − 4ac(d−1))`. With roots `ρ, ρ̄`, `ρ = γ + iδ`: `b/a = −2γ`, `c/a = γ² + δ²`, so the
  discriminant is `≥ 0` iff `(d−1)δ² ≤ γ²`.

**Sector theorem** (`splits_diffOp_X_pow_of_sector`). A real polynomial symbol `h`, `h(0) ≠ 0`, all of whose
complex roots lie in the double sector `(d−1)(Im ρ)² ≤ (Re ρ)²` has `h(D)X^d` real-rooted. The sector is
exact for one conjugate pair, `d ≥ 2` (`splits_diffOp_pairSymbol_iff`).

**Rung** (`jensenNonrealCount_eq_zero_of_rhVerifiedThrough_width`, `…_sq`). The Hadamard approximants of `Ξ`
are real polynomials whose roots are spectral points `γ + iδ` of zeros, `|δ| ≤ w ≤ ½` (`w` the zero width).
Under RH through `T`: `|γ| ≤ T ⇒ δ = 0`; `|γ| > T ⇒ (d−1)δ² ≤ (d−1)w² ≤ T² < γ²`. The sector theorem and
the coefficient limit give `N_d = 0` when `(d−1)w² ≤ T²`, in particular for `d ≤ 4T² + 1`. With the
verified height `67`: `N_d = 0` for `d ≤ 17957`.

**Sharpness** (`exists_pair_beyond_rung`). For `d > 4T² + 1` there is `ρ` with `Re ρ > T`, `|Im ρ| < ½`
whose pair alone has a Jensen polynomial with non-real roots: from verification through `T` and the strip
alone no rung beyond `4T² + 1` follows.

The pair criterion is the Jensen form of de Bruijn's bound: the root near `x = d/γ` sees heat time
`γ²/(2d)`, and `γ²/(2d) ≥ δ²/2` is the sector.

## Log
- 2026-11-13 — created; A20 mechanism found (Walsh closure makes the pair test independent).
- 2026-11-13 — A20 and A19 formalized.
