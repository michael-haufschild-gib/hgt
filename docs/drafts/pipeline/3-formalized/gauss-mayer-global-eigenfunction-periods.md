# Global period realization of actual Mayer solutions

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [PM](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 2–4.

## Statement

For `Re w>0`, `ε²=1`, every actual Mayer disc-algebra solution
`L_w f=ε f+c` has a unique holomorphic continuation `F` to `Re z>−1`.
It agrees with `f` on the original disc interior. Its period
`P(a)=F(a−1)` satisfies, throughout the complex half-plane `Re a>0`,

```text
P(a)=P(a+1)+ε a^(−w) P(1+1/a),
P(a)=ε a^(−w) P(1/a),
P(a)=P(a+1)+(a+1)^(−w) P(a/(a+1)).
```

All powers use the principal logarithm. Constant forcing is retained;
no growth, summability, or continuation hypothesis is imposed on `f`
beyond membership in the actual disc algebra and its source equation.

## Proof

On `Re z>−1/2`, extend the actual regularized transfer by

```text
L_ext f(z)=ζ(w) f(0)+Σ_(n≥1)
  [(n+z)^(−w) f(1/(n+z))−n^(−w) f(0)].
```

Each inverse branch lies in the closed unit disc centered at one and has
norm at most `2/n`. A Cauchy derivative estimate on this smaller disc gives
`|f′|≤4‖f‖`. Together with the principal-power derivative estimate, this
bounds each corrected branch on a compact set by
`C n^(−Re w−1)`. The series converges normally and agrees with the original
regularized operator on its defining disc. The source difference identity
and the identity principle give

```text
L_ext f(z)−L_ext f(z+1)=(1+z)^(−w) f(1/(1+z)).
```

Put `F₁(z)=ε(L_ext f(z)−c)` and define

```text
F(z)=F₁(z+1)+ε(1+z)^(−w) F₁(1/(1+z)),       Re z>−1.
```

Both arguments have positive real part. On the overlap `Re z>−1/2`, the
reciprocal argument lies in the original disc, so the transfer difference
identity proves `F=F₁`. Thus `F` is holomorphic, extends the original
function, and satisfies renewal throughout its domain. The identity
principle gives uniqueness.

Renewal at `a` and `1/a`, together with
`a^(−w)(1/a)^(−w)=1` and `ε²=1`, gives signed inversion. Applying inversion
at `1+1/a` gives the Lewis relation. Positive real parts keep the sums of
arguments in the principal logarithm interval, justifying both power
products for complex arguments.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerExtendedTransfer.lean` certifies
`inverse_mem`, `term_locallyUniform`, `transfer_differentiableOn`,
`transfer_eq_source`, and `transfer_shift`.

`RenormalizedIntersectionTheory/GaussMayerGlobalPeriods.lean` certifies
`extension_differentiableOn`, `extension_eq_plane`, `extension_renewal`,
`period_shift`, `reciprocity`, `three_term`, and `extension_unique`.

Both direct production checks pass without warnings. All twelve public
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Both modules are wired into the mathematical umbrella.

## Unproved boundary-growth conjecture

The previously proposed real-ray asymptotic, for `w≠1`, remains unproved:

```text
F(x)=ε f(0)/(w−1) x^(1−w)−ε c+O(x^(−Re w)).
```

Neither this asymptotic nor its zero-charge decay consequence is part of
the certified theorem. No Maass lift, completeness statement, or
cusp/scattering classification follows from the period identities alone.
