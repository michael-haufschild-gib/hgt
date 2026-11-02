# Limiting compact-core Hecke source

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Statement

Let `u_n=a_n+it_n` be resonant parameters with `a_n→a∈(-1/2,0)` and
`t_n→∞`. On `R={|x|≤1/4, 7/4≤y≤15/8}`, write
`h=2y/(x²+y²)` and `N(u)=||Λ¹E_u||²`.
The weak limit, tested against every continuous function of the real coordinates, is

`|(T₂−λ₂)Λ¹_aut E_(u_n)|²/N(u_n) dμ → (-2a)[2^(2a)y^(1−2a)+h^(1−2a)/2] dμ`.

## Proof

The exact residual is `B(u)[2^u y^(1/2−u)−h^(1/2−u)/√2]`.
Its two diagonal squares are `|B(u)|²[2^(2a)y^(1−2a)+h^(1−2a)/2]`;
the sole cross term has phase `t log(4/(x²+y²))`.

For each fixed positive `y`, this phase is globally real analytic and nonconstant
in `x`. The analytic null-preimage theorem and Fubini make its pushforward on `R`
absolutely continuous. Riemann–Lebesgue removes interference against every
continuous test, including across the stationary line `x=0`.

Joint continuity on compact sets gives convergence in `L¹` of the varying
amplitudes, so the same conclusion holds when `a_n→a`. The functional equation
and nonvanishing in `Re s>1` give `B(u)≠0`; Maass–Selberg gives
`N(u)=|B(u)|²/(-2a)`. Cancelling this factor and applying the hyperbolic coordinate
chart proves the stated limit for the actual automorphic residual.

## Mathematical boundary

This identifies a positive inhomogeneous Hecke source for every admissible rate.
It does not establish invariance, entropy, or a rate selector for the state measure.
## Lean certificates

- `ResonantStates/CoreSourceDephasing.lean`: `coreSourcePhase_absolutelyContinuous`,
  `coreSourcePhase_varying_cos_dephases`.
- `ResonantStates/CoreSourceSquare.lean`: `dyadicEigenResidual_normalized_expansion`,
  `msB_ne_zero_of_negative_re`.
- `ResonantStates/CoreSourceLimit.lean`: `dyadicEigenResidual_core_weak_limit`,
  `coreSourceLimitDensity_pos`.

All modules checked with `lake --old env lean`. Transitive axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`. The limit theorem also covers
boundary limits of the real parameter; strict positivity requires `a<0`.
