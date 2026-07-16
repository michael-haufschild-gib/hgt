# Smooth Waring hypersurfaces have maximal pre-temporal horizons

- **ID:** `smooth-waring-maximal-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM / SMOOTH PROJECTIVE HYPERSURFACE / HYPERTRANSCENDENCE
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [NOVEL COMBINATION PROVISIONAL]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.MvPolynomialWaringSmoothHorizon`

## The theorem

Let

```text
P(x) = sum_i ell_i(x)^d,   d>1,
```

be a Waring polynomial over a characteristic-zero field containing a primitive `d`th root of
unity.  Assume its projective hypersurface is algebraically smooth: every nonzero affine point on
the cone `P=0` has some nonzero evaluated partial derivative.  Then one explicit finite quantum
packet simultaneously satisfies:

1. its complete rational differential-field dependence horizon is exactly `P=0`;
2. its exterior derivation-commutator map is injective on every bivector of the law space.

## Proof

Write the linear forms as the rows of a matrix `a`, so their coefficient map is `a.mulVecLin`.
If a nonzero vector were in its kernel, every `ell_i` would vanish there.  The Waring polynomial
and every partial derivative would then vanish because `d>1`, producing a nonzero singular point.
Smoothness therefore forces the coefficient map to be injective.  The finite quantum Waring
horizon theorem supplies both conclusions.

## Novelty and significance gate

The implication from smoothness to an essential/spanning Waring arrangement is known in the
Waring-rank and hypersurface-singularity literature and is not claimed as new.  The provisional
new statement is its coupling to one exact ordinary hypertranscendence horizon with a faithful
exterior derivation symbol.  Literature searches located generalized-Clifford linearizations and
Waring singularity theory, but not this combined conclusion.

This theorem is stronger than a matrix linearization statement: it simultaneously identifies the
entire differential-dependence locus and proves lossless recovery of every two-plane law channel.

## Physical interpretation gate

The hypersurface is the scalar holographic horizon; the exterior commutator is its lossless
two-plane boundary channel.  The theorem is algebraic and pre-temporal.  A QFT interpretation
still requires an independently justified star/positivity structure and locality law.

## RH impact

Smoothness plus maximal rank is generic and nonselective, so it cannot imply RH.  It eliminates
generic existence from the list of plausible RH bottlenecks and redirects attention to arithmetic
selection, positivity, and minimal-width rigidity.

## Lean verification

Direct check and narrow build pass.  Principal declarations are
`eval_pderiv_mvWaringPolynomial_eq_zero_of_mem_ker`,
`mvWaring_mulVecLin_injective_of_projectivelySmooth`, and
`smoothMvWaring_horizon_and_maximalPrincipalSymbol`.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.
