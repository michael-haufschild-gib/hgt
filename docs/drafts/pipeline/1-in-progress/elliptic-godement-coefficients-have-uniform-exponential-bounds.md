# Elliptic Godement coefficients have uniform exponential bounds

- **Stage:** 1-in-progress
- **Parent:** [Arithmetic unfolding](finite-field-eisenstein-unfolding.md).
- **Target:** Bound all actual finite-field Weyl coefficients exponentially
  in inversion length throughout each fixed Godement chamber, then prove
  absolute convergence of the degree-damped Weyl series.

## Mechanism

The actual adelic logarithmic height is nonnegative. Thus, for `Re(s)≥σ>1`,
`|K_s(a)|≤K_σ(a)` pointwise. The global radial integral implies
`|ζ_K(3^(-s))/ζ_K(3^(-s-1))|≤∫ K_σ`, a finite constant independent of `Im(s)`.

Every positive coroot argument is at least the smaller simple-coroot real
part. Multiplying the uniform bound over the inversion set therefore bounds
the Weyl coefficient by `C^length(w)`, with `C≥1`. In affine A₁ the length
is linear in the translation index. Positive degree rotation contributes
Gaussian decay in that index, which dominates this exponential bound.

## Remaining proof obligations

Audit the global integral, identify its ratio with `arithmeticZetaRatio`,
and formalize the uniform bound and Gaussian summation on the full chamber.
