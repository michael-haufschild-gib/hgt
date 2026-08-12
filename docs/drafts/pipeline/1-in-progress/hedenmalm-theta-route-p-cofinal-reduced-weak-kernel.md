# Hedenmalm theta Route P: cofinal reduced weak kernel (P-G88)

Status: fully proved in Lean; Route P remains open at spectral moment transfer

## Conjecture

Apply P-G84's physical cofinal residual only after P-G86's cumulative inverse incidence. Result
should remain a positive continuous weak Gamma kernel and preserve complete same-depth prime
covariance.

## Verdict

True, unconditionally proved.

## New knowledge

Let `r = 1 - F`, where P-G84 proves `F in (1/2,1)`. Then `r in (0,1/2)`. The physical reduced
kernel is exactly

```text
K_reduced(a,b) = r K_weak(a,b)
               = r sum_e (sum_p a(p,e)) conjugate(sum_q b(q,e)).
```

It is absolutely summable, bounded by half the product of zeroth Deninger height seminorms, and
has nonnegative self-energy. On any two prime-axis deltas at common depth its value is exactly
`r`, including nonadjacent axes invisible to local edge Grams.

Universal order law:

```text
physical depletion -> inverse incidence -> Gram completion.
```

Here scalar depletion commutes with the final global Gram, but not with replacement of inverse
incidence by a local edge Gram.

## Lean realization

File:

- `formal/GaloisForLFunctions/RHTower/GammaValuationSchurCofinalReducedWeakKernel.lean`

Headline declarations:

- `gammaSewnCriticalCofinalResidualFactor_mem`;
- `summable_gammaSewnCriticalCofinalReducedWeakKernelLayer`;
- `norm_gammaSewnCriticalCofinalReducedWeakKernel_lt_half_bound`;
- `gammaSewnCriticalCofinalReducedWeakKernel_self_eq_energy`;
- `gammaSewnCriticalCofinalReducedWeakKernel_axisDelta_sameDepth`.

Direct Lean check and exact module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Next conjecture

Transport this covariance-correct scalar residual to P-G71's compact reciprocal-gap carrier and
test completed seam moments. P-G89 performs that test.

## Honest boundary

P-G88 closes physical scalar reduction at weak covariance level. It does not prove that scalar
reduction is valid after reciprocal-gap spectral pushforward, identify completed Gamma/polar
moments, prove compact germ equality, or prove RH.

