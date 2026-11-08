# A positive totient kernel for Narain target averages

- **ID:** W11-NT
- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Source:** [Target average](../3-formalized/ads3-narain-target-average.md)

## Conjecture

Put `θ(y)=Σ_(n≥1) exp(−πn²y)`, `f(y)=y^(−1/2)θ(y)` and

`Tf(y)=Σ_(q≥1) φ(q) ∫_ℝ f(q²(1+x²)y) dx`.

For every `Y,Z,y>0`, the actual double target average is

`A_YZ(y)=2θ(y/(YZ))+2Z f(yZ/Y)+2Y f(yY/Z)+2YZ Tf(YZy)`.

At unit heights this becomes

`A(y)=2θ(y)+4f(y)+2Tf(y)`.

All terms are positive sources with absolute convergence. This would
express the pole-detecting average through Euler totients and one fixed
Gaussian kernel.

## Equivalent positive Bessel series

A second candidate form isolates one arithmetic coefficient:

`Tf(y)=y^(−1/2) Σ_(m≥1) a_m exp(−πm²y/2) K₀(πm²y/2)`,
`a_m=Σ_(d|m) φ(d)/d`.

Substitute `x=sinh v` in each Gaussian row. Since
`cosh²v=(1+cosh(2v))/2`, its integral is
`exp(−a/2)K₀(a/2)` with `a=πn²q²y`. Regroup `m=nq`.
The coefficient series should be `Σ a_m m^(−w)=ζ(w)²/ζ(w+1)`
for `Re w>1`. This separates the positive analytic kernel from the
arithmetic divisor weights; it supplies no remainder rate.

The corpus defines the real `K₀` as `RHTower.BesselKZero.kMoment 0`
and proves `integral_exp_neg_mul_cosh` in `BesselKZeroMoments`.
The substitution, norm-Fubini and divisor regrouping for this exact
source remain to be formalized.

## Corpus basis and obligations

`narainMellinMean_one_eq` gives the unit-height transform as
`2L₊+4L₋+2L₋²/L₊`, where
`L₊=π^(−s)Γ(s)ζ(2s)` and `L₋=π^(1/2−s)Γ(s−1/2)ζ(2s−1)`.
`MayerCoprimeHeight.totient_series` proves the absolutely convergent
totient series `ζ(w−1)/ζ(w)` for `Re w>2`.
`SelbergThetaTotientHankel.transform_kernel` derives the same completed-zeta
ratio from a literal totient-weighted shift and Cauchy integral.

The proposed operator has Mellin multiplier `L₋/L₊`: scaling contributes
`q^(−2s)(1+x²)^(−s)`, and the Cauchy integral supplies the Gamma ratio.
Prove its norm-Fubini, continuity, exact multiplier and Mellin uniqueness
against the actual Narain average. No decay estimate follows merely from
positivity of this representation.

For uniqueness, apply `mellinInv_mellin_eq` to the difference on `Re s=2`.
Its Mellin transform is zero on that line, so vertical integrability is
automatic; only the already required source convergence and continuity
remain. No new vertical strip bound is needed for this identification.

## Gates

- [ ] 0 → 1: audit normalization and identify all convergence/uniqueness inputs.
- [ ] 1 → 2: dependency-closed paper proof of the actual-source identity.
- [ ] 2 → 3: Lean formalization and transitive axiom audit.
