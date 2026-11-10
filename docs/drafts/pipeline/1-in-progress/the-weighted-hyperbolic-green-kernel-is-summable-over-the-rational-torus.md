# The weighted hyperbolic Green kernel is summable over the rational torus

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: an actual Green kernel on the torus quotient.
- **Target:** Absolute convergence of the rational-torus orbit sum of the weighted
  mixed Green kernel, with the canonical Robin value at coincident points.

## Mechanism

Let `a²=λ+1/4`, with the actual weighted adjacency
`A=Σ_p p⁻² A_p`. For `s>1/2`, define the normalized restricted radial product
`h_s(x,y)=Π_p p^(−s d_p(x_p,y_p))` and
`E(s)=Σ_p p⁻²(p^s+p^(1−s))`.

On a fixed interval `1/2≤s≤3/4`, the summands are bounded by a constant
multiple of `p^(−5/4)`. Continuity of the sum, and `E(1/2)=λ`, should supply
`s>1/2` with `E(s)<a²`. Put `κ=√(a²−E(s))>0` and `c=a−κ`.
The local Green identities give `A h_s≤E(s)h_s`.

For each finite Dirichlet section, positivity of the root iteration and
`E(s)+c²=2ac` imply `R_F h_s≤c h_s`. The finite-section limit would pass this to
the full remainder `R=aI−√(a²I−A)`. On distinct finite
vertices, the identity term of `exp(rR)` vanishes, hence

`0≤K(r;x,y)≤e^(−ar)(e^(cr)−1)h_s(x,y)/(4π sinh r)≤c h_s(x,y)/(4π)`.

The same bound at `r=0` follows from the Robin entry `R(x,y)/(4π)`.
This removes the apparent `1/r` singularity at archimedean near-collisions;
no Diophantine separation of the archimedean orbit is needed for this bound.

On the degree configuration, the rational torus with `q=a₀/b₀` in lowest
terms changes the local apartment coordinate by `2v_p(q)`. The triangle
inequality therefore bounds the radial product by
`C_(m,n) (a₀ b₀)^(−2s)`. Its sum over positive numerator-denominator pairs
converges because `2s>1`. Terms with equal finite vertices must be separated;
their profile equals one, so profile summability itself makes this exceptional
set finite. Their full collision values use the canonical Robin prescription.

For arbitrary restricted vertices, the local triangle inequality should give
the same height bound, with constant
`Π_p p^(s(d_p(base,x_p)+d_p(base,y_p)))`, a finite product.
The same finite-exception argument applies to arbitrary restricted vertices.
It requires no separate classification of the torus stabilizer.

## Remaining proof obligations

- Verify the variable-exponent radial product and its all-prime supersolution identity.
- Prove the spectral margin `E(s)<λ+1/4` for some `s>1/2` without numerical estimates.
- Prove the uniform root and Green entry bounds from finite sections.
- Establish the torus height bound on the full carrier, finiteness of the equal-fibre exception,
  absolute summability, symmetry, and descent to the quotient.
- Formalize each claimed limit and bound; the argument above is not yet Lean verified.

## Boundary

This is the standard branch for the specified weighted operator. It does not
identify the quotient kernel or its Robin diagonal with Weil's form. The accepted
invariant-gluing obstruction remains in force.
