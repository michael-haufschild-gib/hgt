# Limiting compact-core Hecke source

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [arithmetic measure rigidity](resonant-state-arithmetic-measure-rigidity.md).

## Statement

Let `u_n=a_n+it_n` be resonant parameters with `a_n→a∈(-1/2,0)` and
`t_n→∞`. On `R={|x|≤1/4, 7/4≤y≤15/8}`, write
`h=2y/(x²+y²)` and `N(u)=||Λ¹E_u||²`.
The proposed weak limit is

`|(T₂−λ₂)Λ¹_aut E_(u_n)|²/N(u_n) dμ → (-2a)[2^(2a)y^(1−2a)+h^(1−2a)/2] dμ`.

## Proof mechanism

The exact residual is `B(u)[2^u y^(1/2−u)−h^(1/2−u)/√2]`.
After squaring, the only cross term has phase `t log(4/(x²+y²))`.
For each fixed positive `y`, this phase is globally real analytic and nonconstant
in `x`; its pushforward is absolutely continuous. Fubini and the corpus
Riemann–Lebesgue theorem remove the cross term even across `x=0`.
Compact continuity controls the varying real parameter. The Maass–Selberg norm
and nonvanishing of `B(u)` supply the actual state normalization.

## Mathematical boundary

This identifies a positive inhomogeneous Hecke source for every admissible rate.
It does not establish invariance, entropy, or a rate selector for the state measure.
## Lean status

`ResonantStates/CoreSourceDephasing.lean` is checked: the phase pushforward is
absolutely continuous, and interference vanishes for jointly continuous amplitudes
with a convergent real parameter. This holds on the full rectangle, including `x=0`.

`CoreSourceSquare.lean` is checked: `dyadicEigenResidual_normalized_expansion`
cancels the nonzero Weyl coefficient against the exact Maass–Selberg norm.
`CoreSourceLimit.lean` contains the weak-limit proof; its audit remains open.
