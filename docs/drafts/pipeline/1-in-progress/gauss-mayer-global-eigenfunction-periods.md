# Global period realization and boundary charges of actual Mayer eigenfunctions

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [PM](route-pm-mayer-scattering-and-escape.md), Mayer 2–4.
- **Input:** Signed period relations of all actual constant-forced solutions.

## Target

For `Re w>0`, `ε²=1`, and an actual disc-algebra solution
`L_w f=ε f+c`, construct its unique holomorphic continuation to `Re z>−1`.
Its period `P(a)=f(a−1)` should satisfy signed inversion and the Lewis
relation throughout `Re a>0`. For `w≠1`, prove on the positive real ray

```text
f(x)=ε f(0)/(w−1) x^(1−w)−ε c+O(x^(−Re w)).
```

Consequently every actual eigenfunction with zero boundary charge decays
as `O(x^(−Re w))`; every negative-unit eigenfunction has that property.
This is the needed growth control for a geometric cusp/scattering
realization. Neither a Maass lift nor its completeness is assumed.

## Construction to audit

First extend the actual regularized branch series to `Re z>−1/2`:

```text
L_ext f(z)=ζ(w) f(0)+Σ_(n≥1)
  [(n+z)^(−w) f(1/(n+z))−n^(−w) f(0)].
```

Every inverse branch lies in the unit disc centered at one. On compact
sets, the existing Cauchy derivative bound for `f` and the principal-power
derivative should give a summable `n^(−Re w−1)` majorant. Normal convergence
would prove holomorphy and equality with the actual source operator.
The source equation then defines the continued `f`.

Separate the first branch for a second continuation to `Re z>−1`.
Its reciprocal argument has positive real part and therefore belongs to
the first continuation domain; all remaining branches stay in the original
disc. Agreement on the overlap must be proved before gluing. The identity
principle then continues the already established real period relations.

For the boundary law, split the transfer series into `f(0)` times the
continued Hurwitz series and the correction `f(1/(n+x))−f(0)`.
The latter is bounded by a convergent tail of `(n+x)^(−Re w−1)`.
The required Hurwitz asymptotic and every interchange remain proof
obligations. The displayed targets are not yet certified.
