# R47 - sharp explicit-formula cutoff instability

Status: dead end / standard explicit-formula smoothing warning.

Random source chain:
- seed RandomNode: coupled waiting times can break the usual factorization of multi-time probabilities used in standard renewal calculations
- broad topic RNG: 7, non-Poissonian event statistics
- NODE RNG: 3, heavy-tailed waiting times can make sample means unstable and convergence painfully slow
- target-file RNG: 3, `docs/consolidated/01-landscape-and-weld-geometry.md`
- target-topic RNG: 5, explicit formula as constraint linking zeros, primes, and the archimedean term
- scientific-method RNG: 22, nearby false statements
- perturbation-method RNG: 5, make visual

## Transfer

Nearby false statement:

```text
a large sharp zero cutoff gives a stable pointwise explicit-formula estimate.
```

The NODE suggests treating this like a slow-converging heavy-tail sample mean.
The target demands the explicit formula as a distributional constraint, not a
pointwise flow estimate.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r47-explicit-formula-cutoff-instability.py
```

For `psi(x)` approximated by zeros up to sharp cutoff `N`, late blocks still
move the result materially:

```text
x=10000, psi=10013.396693
N= 10 err=  7.925458
N= 20 err= 10.285026
N= 50 err=  9.850064
N=100 err=  5.700203
N=150 err=  3.146570
N=200 err=  7.499819
```

Last-block movements:

```text
x=10000, zeros  51-100: +4.149862
x=10000, zeros 101-150: +2.553633
x=10000, zeros 151-200: -4.353250
```

Visual reading:

```text
N:    10      20      50     100     150     200
err: +7.93  +10.29   +9.85   +5.70   +3.15   +7.50
```

## Verdict

Dead end for non-reducing count. The warning is correct but classical: sharp
cutoffs are bad pointwise estimators of the explicit formula; the constraint
belongs to smoothed/distributional test functions. No new explicit-formula
object or seam invariant was produced.
