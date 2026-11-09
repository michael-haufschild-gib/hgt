# Critical adelic orbit and global renormalization

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B133.

For a reduced positive rational `q=a/b<1`, the diagonal torus displacement
has real distance `2 log(b/a)` and finite apartment distances `2|v_p(q)|`.
Multiplying `2πG_{1/2}` by the normalized critical finite Green factors
gives `b⁻²/(1−(a/b)⁴)`. The identity orbit is excluded.

**Target.** The sum of `b⁻ˢ/(1−(a/b)⁴)` over `0<a<b`, `(a,b)=1`,
converges exactly when `s>2`. Thus height damping of the coupled critical
kernel converges exactly for positive damping; its removal needs a global
orbit subtraction in addition to the free-space Robin subtraction.

For convergence, set `t=s/2>1` and bound the summand by
`a⁻ᵗ(b−a)⁻ᵗ`; the primitive cone injects into the positive lattice.
For divergence at `s=2`, the primitive pairs `(a,a+1)` contribute at least
`1/(4(a+1))`. Monotonicity gives divergence for every `s≤2`.

This tests the multiplicatively coupled local Green kernel. It does not
identify it with the sum of local channels or with Weil's form. The finite
part and its comparison with Weil's diagonal remain open.

## Finite-part target

The exact decomposition
`1/(1−r⁴)=1/(4(1−r))+1/(4(1+r))+1/(2(1+r²))`
separates the singular kernel from the smooth remainder `h(r)`.
Its integral is `c₀=log 2/4+π/8`. Before imposing coprimality, a height
row is `b H_{b−1}/4+b c₀+O(1)` by monotone Riemann sums.
Thus the all-pairs height cutoff should have a finite part after subtracting
`(log N)²/8+(γ/4+c₀)log N`. Primitive extraction divides the homogeneous
Dirichlet series by `ζ(s)`; proving this comparison would determine the
primitive orbit's counterterms from its geometry. These finite-part claims
remain to be formalized.

An exact primitive subtraction avoids choosing a logarithmic asymptotic gauge.
At height `b`, subtract the collision row
`(4b)⁻¹ Σ_{0<a<b,(a,b)=1} a⁻¹` and the density row
`c₀ φ(b)/b²`. Möbius inversion should express the remaining row as
`b⁻² Σ_{d|b} μ(d) E(b/d)`, where
`E(n)=Σ_{0<a<n} h(a/n)−n c₀` is uniformly bounded by monotone quadrature.
Absolute convergence then gives the global remainder
`ζ(2)⁻¹ Σ_{n≥1} E(n)/n²`, with the height-one convention handled explicitly.
This is a candidate finite part for the product profile, not an identification
with Weil's diagonal. The primitive quadrature identity and convergence are open.
