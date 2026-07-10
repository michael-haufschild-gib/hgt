# Prime barycentric coefficients diverge under canonical exhaustion

- **ID:** prime-barycentric-coefficient-divergence
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `fe-paired-prime-jet-barycentric-rigidity.md`
- **Statement:** `[PROVED]` Fix a prime `p₀`.  In the unique FE-paired interpolation packet on
  all primes `p ≤ X`, the coefficient at `p₀` tends to infinity in magnitude as `X → ∞`.

## Goal

Rule out the last finite-flow interpretation.  Even if every coefficient is recomputed at every
support size, canonical prime exhaustion has no coefficientwise finite limit.

## Gates

- [x] 0 → 1 in-progress: precise support exhaustion and exact product formula
- [x] 1 → 2 fully-proven: Chebyshev proof with no open dependency
- [x] 2 → 3 formalized: exact Lean target built and capstone axioms audited
- [ ] 3 → 4 publication-ready: integrate with the finite/all-orders boundary theorem

## Formula

Put `c = (log p₀)^2`.  The magnitude of the barycentric coefficient at `p₀` on the prime support
`(1,X]` is

`(1/(2 log p₀)) * ∏_{q≤X, q≠p₀, q prime} (log q)^2 / |c-(log q)^2|`.

The factors from primes below `p₀` form a fixed positive constant.  Every factor above `p₀` is

`(log q)^2 / ((log q)^2-c) = 1 + c/((log q)^2-c) > 1 + c/(log q)^2`.

## Prime-density theorem

Define

`S(X) = ∑_{p≤X, p prime} 1/(log p)^2`.

For `p≤X`, positivity and monotonicity of the logarithm give

`log p/(log X)^3 ≤ 1/(log p)^2`.

After summation, the left side is `θ(X)/(log X)^3`.  The formalized Chebyshev bound gives

`(X-1)log 2 - log(X+2) - 2sqrt(X)log X ≤ θ(X)`.

The lower bound divided by `X` tends to `log 2`, while `X/(log X)^3` tends to infinity.  Hence
`S(X) → ∞`.  Removing the finitely many primes at most `p₀` preserves divergence.

## Product theorem

For nonnegative `u_i`,

`1 + ∑ u_i ≤ ∏ (1+u_i)`.

Applying this with `u_q=c/(log q)^2` shows that the positive tail product is bounded below by

`1 + c * ∑_{p₀<q≤X} 1/(log q)^2`,

which tends to infinity.  Multiplication by the fixed positive lower-prime factor proves divergence
of the full coefficient magnitude.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/PrimeBarycentricCoefficientDivergence.lean`

Capstones:

- `tendsto_primeReciprocalLogSqSum_atTop`
- `one_add_logSq_mul_tailSum_le_primeBarycentricTailGrowth`
- `tendsto_primeBarycentricTailGrowth_atTop`
- `primeBarycentricCoefficientMagnitude_eq_head_mul_tail`
- `tendsto_primeBarycentricCoefficientMagnitude_atTop`

The exact target `GaloisForLFunctions.RHTower.PrimeBarycentricCoefficientDivergence` builds
successfully.  The audited capstones have axiom footprint
`[propext, Classical.choice, Quot.sound]`.

## Novelty and significance

- **Novel:** the parent theorem proved coordinatewise change under one support extension.  This
  theorem proves divergence along the canonical all-prime exhaustion, even with global
  recomputation at every stage.
- **Significant:** no sequence of exact finite FE-paired packets converges coefficientwise to fixed
  local Euler data.  The finite approximation is not an approximation scheme for the source.
- **RH status:** this is not an RH proof.  It proves that a surviving all-prime Euler/Gamma object
  must be a genuinely non-finite renormalized constraint, not a limit of exact finite packets.
