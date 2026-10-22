# Prime--archimedean tensor-dispersion rigidity universality law

Status: paper proof complete; exact `lake env lean` audit passed.

## Lean sources

- `finitePrimeArchPairPowerSum_eq_mul`
- `two_mul_dispersion`
- `dispersion_nonneg`

## Survivor

For the pair-product alphabet `(x_p y_j)`, the curvature dispersion
`D = M₂ M₄ - M₃²` obeys the exact product law

```text
D(x tensor y)
  = D(x) M₂(y) M₄(y) + M₃(x)² D(y).
```

For nonempty positive finite alphabets this yields a rigidity classification: pair-product
dispersion vanishes if and only if both factor alphabets are constant on their supports. Thus a
single tensor curvature statistic detects nontrivial variation in either the prime or the
archimedean channel.

The tensor source proves only power-sum factorization and negative-real root location. The
low-temperature source proves dispersion positivity for one arbitrary weighted alphabet. Neither
states the product decomposition or its two-factor equality case.

## Proof skeleton

Substitute the tensor factorization into `M₂ M₄ - M₃²` and add/subtract
`M₃(x)² M₂(y) M₄(y)`. The one-factor pairwise-dispersion identity shows nonnegativity and, under
strict positivity, classifies equality by pairwise constancy. Nonempty positive factors make both
coefficients in the product decomposition strictly positive, so vanishing forces both component
dispersions to vanish.

## Novelty audit

Pending post-formalization literature search.
