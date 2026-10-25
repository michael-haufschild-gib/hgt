# Exponential source mass controls the full prime sum

- **ID:** exponential-source-mass-controls-the-full-prime-sum
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II; global arithmetic majorant construction.
- **Statement:** The full prime form of any continuous compact real source is at most twice the convergent three-halves von Mangoldt mass times its exponential position mass.
- **Status:** `[PROVED HERE]`; actual-file Lean check and transitive axiom audits passed.

## Exact statement and proof

Put `w(f)=integral (exp(|t|)f(t))²` and
`S=sum_n Lambda(n)/n^(3/2)`. For every real `a`,

`|integral f(t)f(t-a)| <= exp(-|a|) w(f)`.

The inequality `|a|<=|t|+|t-a|` bounds the scaled absolute integrand by
`g(t)g(t-a)`, where `g(t)=exp(|t|)|f(t)|`. Translation Cauchy–Schwarz bounds
its integral by `integral g²=w(f)`. All integrands have compact support.

At the prime lag `a=log n`, `n>=2`, each of the two correlations is at most
`w(f)/n`. Multiplication by the nonnegative prime atom and summation gives

`primeSum(f) <= 2 S w(f)`.

The original prime series is summable by compact support; the dominating
series is the already certified three-halves von Mangoldt series. Terms at
`n=0,1` vanish. Thus no aperture parameter or unproved summation interchange
is present.

## Lean certificate

Module: `ArithmeticCastelnuovoSeveri/ExponentialSourceMassControlsTheFullPrimeSum.lean`.

- `abs_correlation_le_exp_neg_mul_sourceMass`
- `primeSum_le_two_threeHalvesMass_mul_exponentialSourceMass`

Both endpoints passed `#print axioms` with exactly
`[propext, Classical.choice, Quot.sound]`. Final check:

```
lake --old env lean GaloisForLFunctions/ArithmeticCastelnuovoSeveri/ExponentialSourceMassControlsTheFullPrimeSum.lean
```

Temporary audit commands removed; ACS umbrella and README wired. No olean
was built for this check. The global cone theorem consuming this bound is
tracked separately in `../2-fully-proven/a-global-arithmetic-majorant-for-the-scaling-surface.md`.
