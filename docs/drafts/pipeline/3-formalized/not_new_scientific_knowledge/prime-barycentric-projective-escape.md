# Prime barycentric packets escape projectively

- **ID:** prime-barycentric-projective-escape
- **Stage:** 3-formalized (not new scientific knowledge)
- **Type:** THEOREM (paper + Lean, unconditional)
- **Parent:** `prime-barycentric-coefficient-divergence.md` (same folder)
- **Statement:** `[PROVED]` For fixed primes `p<q`, the ratio of the canonical exact coefficient
  magnitudes satisfies `|a_q(x)|/|a_p(x)| → ∞` along prime exhaustion `x → ∞`.

## Result

No common scalar renormalization turns the divergent exact finite packets into a nonzero
coefficientwise limit: a scalar-normalized packet cannot retain finite nonzero coefficients at two
fixed primes, because their ratio diverges. The finite interpolation flow has neither an ordinary
nor a projective coefficientwise limit.

## Proof

Write `x_p=(log p)^2` and `x_q=(log q)^2`. Splitting the canonical support at `q` factors each
coefficient magnitude into its value at `q` times an upper-prime growth product; the quotient of
the two growth products telescopes to the relative tail product over primes `q<r<=x` of

`(x_r-x_p)/(x_r-x_q) = 1 + (x_q-x_p)/(x_r-x_q) > 1 + (x_q-x_p)/x_r.`

First-order terms dominate: `1 + Σu_r ≤ Π(1+u_r)` for nonnegative `u_r`. Chebyshev's theta lower
bound alone forces `Σ_{p≤x} 1/(log p)^2 → ∞` (via `theta(x)/(log x)^3 ≤ Σ 1/(log p)^2`), hence the
tail sum and therefore the relative tail product diverge. The base factor at `x=q` is a fixed
positive constant, so the full ratio tends to infinity.

## Lean certificate

`formal/GaloisForLFunctions/RHTower/PrimeBarycentricProjectiveEscape.lean`, wired into the
`RHTower` umbrella:

- `primeBarycentricRelativeTailGrowth`, `primeBarycentricUpperGrowth`,
  `primeBarycentricProjectiveRatio` — the exact finite objects;
- `one_add_logSqDiff_mul_tailSum_le_primeBarycentricRelativeTailGrowth` — the first-order lower
  bound;
- `primeBarycentricCoefficientMagnitude_eq_at_mul_upperGrowth` — the support-splitting
  factorization;
- `tendsto_primeBarycentricRelativeTailGrowth_atTop` — divergence of the relative tail product;
- `tendsto_primeBarycentricProjectiveRatio_atTop` — **projective escape**, the card statement.

Axiom audit (2026-07-12): every declaration above depends only on
`propext, Classical.choice, Quot.sound`.

## Novelty verdict

Not new scientific knowledge. The proof is an elementary product-divergence argument downstream of
the already-banked coefficient divergence; a competent analyst produces it when prompted. Its value
is as a certified route-closer: it upgrades "the coefficients diverge" to "no projective/scalar
renormalization can repair them."

## What this opens

Any completed all-prime source must use a genuinely different renormalized constraint — not a
scalar rescaling of the finite interpolation flow. The successor object is the fixed completed-flux
germ: interpolate the germ data directly under a constraint that never passes through the divergent
local-coefficient chart.

## Gates

- [x] 0 → 1 in-progress: exact relative factor and Chebyshev provider identified
- [x] 1 → 2 fully-proven: complete paper proof (support-splitting + first-order domination +
  unconditional Chebyshev divergence)
- [x] 2 → 3 formalized: `PrimeBarycentricProjectiveEscape.lean`, axiom-clean
- [ ] 3 → 4 publication-ready: integrate with the fixed completed-flux germ

## Log

- 2026-07-10 — opened with exact relative factor and Chebyshev provider.
- 2026-07-12 — paper proof completed and matched to the committed Lean module; axiom audit passed;
  card moved to 3-formalized (not new scientific knowledge).
