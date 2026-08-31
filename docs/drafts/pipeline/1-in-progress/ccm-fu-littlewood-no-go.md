# CCM-FU Littlewood no-go

## Chain

`CCM-FU bound ↔ RH ∧ PsiRemainderSquareRootBounded`; prove
`RH → ¬PsiRemainderSquareRootBounded`, then negate CCM-FU and central unit-Riesz bounds.

## Facts

- Lean: exact CCM-FU classification is proved.
- Lean: Deninger explicit formula holds for every smooth compact positive-time test.
- Lean: multiplicity-exact Xi divisor has cofinally unbounded Poisson-Hilbert packets.
- Lean: compact autocorrelation has nonnegative squared Fourier transform.
- Lean: `PsiRemainderSquareRootBounded` iff normalized Chebyshev error is bounded on the full late
  continuous ray.
- Lean: that condition uniformly bounds every late-supported integrable detector by its `L¹` norm.
- Lean: one explicit normalized compact autocorrelation yields Deninger weights with coherent mass
  `≫ log T` at reciprocal dyadic scale.
- Lean: under RH, its full multiplicity-exact Deninger spectral sum equals the summable phase packet
  and is cofinally unbounded at arbitrarily late translations.
- Literature: Littlewood's PNT-error omega theorem is stronger than the target no-go.

## Open core

Prove `PsiRemainderSquareRootBounded` uniformly bounds the same translated Deninger explicit-formula
response; contradiction then kills CCM-FU.
