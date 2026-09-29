# Exact one-direction compensation for the literal prime curvature

- **ID:** RW-PRIME-CURVATURE-ONE-DIRECTION
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); Lean audit pending
- **Source:** RW prime-Bochner frontier and `CCMPrimePoleNegativeCurvature`.
- **Statement:** At aperture `log(21/10)` and point `log 2`, literal prime Γ₂ is exactly four positive squares minus a strictly positive coefficient times one sample difference squared. Vanishing of that difference restores nonnegative curvature without improving the actual constrained Weil ground infimum.

## Exact coefficients and paper proof

Put `l=log 2`, `m=log 3`. Subtract `f(log 2)` from the other five stencil values; denote the resulting values at multiplicative positions `1,2/3,1/2,4/3,3/2` by `A,B,C,D,E`, respectively. Actual cutoff rows, already kernel-checked in the predecessor, give

`Γ₂ = (7lm/72)(D-2B)² + (5lm/72)(E-2C)² + αA² + βB² + γC² + bAB + cAC + eBC`,

where

`α=31l²/36-5lm/54`, `β=53m²/162-7lm/27`, `γ=13l²/24-5lm/36`,

`b=10lm/27`, `c=-l²/2`, `e=5lm/18`.

This is an exact algebraic expansion of the four actual rows, retaining all prime powers, pole-profile rates and cutoff indicators.

The elementary corpus logarithm inequalities `l>0`, `m>0`, `5m<8l` imply

`α > (7/10)l²`, `γ > (3/10)l²`.

Consequently `4αγ-c² > (59/100)l⁴ > 0`. Let

`δ=γ-c²/(4α)>0`, `z=e-bc/(2α)`,

`κ=β-b²/(4α)-z²/(4δ)`.

Completing two squares yields the exact identity

`Γ₂ = (7lm/72)(D-2B)² + (5lm/72)(E-2C)²`

`      + α(A+(bB+cC)/(2α))² + δ(C+zB/(2δ))² + κB²`.

The existing negative smooth witness forces `κ<0`: all four square terms are nonnegative, so `κ≥0` would contradict its exact negative curvature. Thus `K=-κ>0` is an exact rank-one compensation coefficient:

`Γ₂(f) ≥ -K(f(log(2/3))-f(log 2))²`.

It is sharp: prescribe `B=1`, `C=-z/(2δ)`, `A=-(b+cC)/(2α)`, `D=2`, `E=2C`, and central value zero. All four squares vanish, giving `Γ₂=-K`. The finite-source interpolation theorem realizes these exact physical values with exact pole constraints and arbitrarily small complete form norm; no abstract finite graph is substituted for the source.

On `B=0`, curvature is nonnegative. Equality then forces all six samples equal: the two completed square terms force `C=A=0`, and the outer terms force `D=E=0`. In particular the constraint that both physical samples at `log 2` and `log(2/3)` vanish enforces `B=0` for the real pole-normalized source observable. Its constrained smooth Rayleigh infimum remains exactly `μ₀(a)` by `ccmSampledPolarRayleigh_inf_eq`.

## Strongest positive survivor and relevance

The previous blanket prime-curvature no-go exposes a single literal sample difference carrying all negativity, an exact optimal coefficient, and a codimension-one nonnegative sector with its full equality classification. Yet that local repair has zero capacity in the complete energy topology. This identifies precisely why locally repaired prime curvature cannot, by itself, raise RW's source floor. Integrated archimedean/prime/polar compensation remains open.

## Novelty audit

Current corpus search: `prime pole curvature one negative direction completion squares six sample stencil`; exhaustive `rg` supplements ranked retrieval. Predecessors contain a negative witness and degree-envelope lower bound, not this exact one-direction decomposition or its compensated equality case. No generic claim of new Schur-complement algebra is made.

Targeted public searches for Weil prime curvature, rank-one compensation and pole-profile Bochner curvature found no exact match. Returned primary research pages require inspection; absence from all literature or inaccessible training data cannot be certified. A matching theorem retires novelty and triggers another conjecture.

## Formal audit

Pending. New leaf intended: `CCMPrimePoleCurvatureRankOne.lean`. Final leaf checks, standard-axiom audit and umbrella wiring required. No numerical eigensolver, new axiom, heartbeat increase or full build.
