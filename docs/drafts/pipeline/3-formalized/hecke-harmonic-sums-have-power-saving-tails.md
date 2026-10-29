# Hecke harmonic sums have power-saving tails

- **ID:** hecke-harmonic-sums-have-power-saving-tails
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Mertens programme](hecke-character-mertens-via-ideal-hyperbola.md)
- **Lean:** `GaloisForLFunctions/HeckeLFunctions/HeckeHarmonicSumsHavePowerSavingTails.lean`
- **Statement:** For every nontrivial ray class character and `delta=1/(2[K:Q])>0`, the actual harmonic ideal sums satisfy `|L(1,psi)-Spsi(N)| <= C*(N+1)^(-delta)`. Their logarithmically weighted counterparts are uniformly bounded.

## Proof

Actual ray-class coefficient sums are `O(x^alpha)`, with
`alpha=1-1/[K:Q]`. Put `sigma0=1-delta>alpha`.
`exists_norm_sum_term_le` bounds the partial sums of
`a(n)=LSeries.term(heckeCoeff,sigma0,n)` by `M`.
Every shifted partial sum is at most `2M` by subtraction.

The existing decreasing-weight Abel inequality applied to
`(N+j)^(-delta)` bounds every finite tail by `2M*N^(-delta)`.
The already proved Dirichlet-series convergence identifies its limit with
`heckeLCont(1,psi)`. Starting at `N+1` gives
`exists_norm_heckeLCont_one_sub_harmonic_le`.

For logarithmic sums the weight `log(n)/n^delta` is nonnegative and
decreases once `n>=exp(1/delta)`, by
`Real.log_div_self_rpow_antitoneOn`. Split off the finite initial segment
and apply the same Abel inequality to the shifted tail. This proves
`exists_norm_heckeLogarithmicHarmonicSum_le`.

Both results concern the actual Hecke coefficients. No bound on ordinary
partial sums stronger than ray-class counting is assumed.

## Audit

The complete scratch passes without warnings. Both exported estimates
have transitive axiom sets `[propext, Classical.choice, Quot.sound]`.
The module is wired into the Hecke umbrella. The final direct source check
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeHarmonicSumsHavePowerSavingTails.lean`
passes without warnings. Its olean is generated for the written
weighted hyperbola consumer. No umbrella was compiled.
