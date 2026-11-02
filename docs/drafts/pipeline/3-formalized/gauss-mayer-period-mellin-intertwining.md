# Mellin transform of the actual Mayer period

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3–4.

## Theorem

For `Re u>1` and `Re(w−u)>1`, the absolutely convergent identity is

```text
∫₀∞ a^(u−1) ζ₂(a,1;w,a+1) da
  = Γ(u)Γ(w−u)ζ(u)ζ(w−u)/Γ(w).
```

The actual period on its certified real segment is
`Φ_w(a)=ζ(w)(1+a^(−w))+2ζ₂(a,1;w,a+1)`.
Thus the integral concerns its actual cone term, with both axes removed.

## Proof mechanism

Write `b(t)=1/(exp(t)−1)` and `f_w(y)=y^(−w)b(1/y)`. The Barnes heat
representation and inversion of the positive integration variable give

```text
Γ(w)ζ₂(a,1;w,a+1)
  = ∫₀∞ t^(w−1)b(t)b(at) dt
  = ∫₀∞ f_w(y)b(a/y) dy/y.
```

The last expression is actual multiplicative convolution. The ray
Mellin transform is `Γ(u)ζ(u)`; inversion and shifting give
`M f_w(u)=Γ(w−u)ζ(w−u)`. Both transforms converge absolutely under the
stated inequalities. The existing Mellin convolution theorem supplies
absolute convergence of the cone transform and the product of these
two values. `Γ(w)≠0` permits division. The certified Barnes boundary
identity then identifies the cone with the actual period minus its axes.

## Further bridge to test

The quadratic Eisenstein lattice along the imaginary axis should have
the same zeta factors with half-argument Gamma weights. Comparing actual
integrals, rather than only their scalar factors, is needed for a
period-to-automorphic transform.

## Boundary

No Hermitian intertwining is proved by matching scalar zeta factors.
Continuation, endpoint subtractions, and the actual automorphic transform
remain obligations. The stated convergence inequalities are incompatible
with `Re w<1`; they do not justify continuing the integral there.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerPeriodMellin.lean` certifies
`hasMellin_gamma_cone`, `mellin_cone`, `mellinConvergent_cone`, and
`period_axes_decomposition`, including the actual convolution identity.
Five axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
