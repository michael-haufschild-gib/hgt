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
- Literature: Littlewood's PNT-error omega theorem is stronger than the target no-go.
- Current proof route: translated compact autocorrelation; zero-band mass is `≫ log T`, while a
  square-root Chebyshev bound makes its arithmetic pairing uniformly bounded.

## Open core

Identify a translated compact-autocorrelation Deninger test with its Xi spectral sum, then combine
its growing band mass with the proved uniform arithmetic detector bound.
