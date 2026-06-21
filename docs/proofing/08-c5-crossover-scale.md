# C5 Proof Attempt: A Genuine Crossover Scale sigma*

Source: `docs/consolidated/08-conjectures-required.md` §1.

Claim status: `[CONJECTURE]`.

## Target Claim

There is a sharp crossover `sigma* in (1/2,1)` where weld coherence changes
from alive to dead, possibly near `sigma* = 3/4`, and the transition is
non-analytic in the chosen statistic.

## Proof Attempt

A direct analytic route fails. Any statistic built from a finite number of
absolutely convergent Dirichlet/Euler expressions is real-analytic in `sigma`
on every compact interval inside `(1/2, infinity)` where the defining series
converges uniformly. In particular, for a finite prime cutoff `S`,

```text
P_S(s) = - sum_{p in S} log(p) p^{-s} / (1 - p^{-s})
```

is analytic in `s`, hence any smooth statistic of finitely many values of
`P_S`, `Gamma`, and their derivatives is analytic in `sigma` away from zeros
and branch singularities.

Therefore a non-analytic kink at an interior `sigma*` cannot be produced by
fixed finite cutoffs or by any uniformly convergent family of analytic
statistics. A genuine C5 transition must come from a nonuniform limit:

```text
N -> infinity, window -> infinity, threshold -> critical value,
or an eigenvalue crossing in a limiting operator.
```

## Weakened Theorem Proved Here

**Theorem C5-W.** Let `F_N(sigma)` be a sequence of real-analytic statistics on
an open interval `I`, converging locally uniformly with all derivatives needed
to a limit `F`. Then `F` is real-analytic on `I`. Consequently, a non-analytic
crossover in `(1/2,1)` requires failure of such local-uniform analytic
convergence or a limiting spectral/threshold operation outside this class.

This follows from the standard Weierstrass theorem for locally uniform limits
of holomorphic functions, applied after complexifying `sigma` in a small
neighborhood avoiding singularities.

## Attack As False

The observed fade may be smooth. The prime variance

```text
sum_p p^{-2 sigma}
```

has its singular boundary at `sigma = 1/2`; it does not by itself create an
interior singularity at `3/4`. Thus `sigma* = 3/4` is unsupported unless tied to
a new limiting operator, a thresholded percolation statistic, or a nonuniform
thermodynamic limit.

## Missing Input

1. Define the statistic whose non-analyticity is claimed.
2. Prove the statistic is a genuine limiting object, not a finite-cutoff
   analytic observable.
3. Show a kink/eigenvalue crossing/scaling law at `sigma*`.
4. Show the scale is not an artifact of threshold selection.
