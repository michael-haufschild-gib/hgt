# Finite exceptional subtraction at escaping heights

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Euler–FE transport: removing the infinite Gamma counterterm.

## Theorems

Suppose a finite set `F` of actual zero copies contains every zero with
real part greater than `θ`, and `0<σ≤1`, `θ<σ`. On the regular high strip
`σ≤Re s≤1`, `Im s≥4`, at fixed positive distance from the divisor,

`|G_s(y)+Σ_{ρ∈F}½Γ((ρ−s)/2)y^(−(ρ−s)/2)−e^(−y)(A(s)−ξ′/ξ(s))|`
`≤C[y+y^((σ−θ)/2)](1+log Im s)`, for `0<y≤1`.

The infinite complementary field is explicitly bounded. The actual
finite exceptional layer under `¬AAL` supplies this estimate on a whole high strip
strictly left of the top.

## Proof mechanism

For `a=ρ−s`, `−1<Re a<1`. Gamma recursion gives
`½Γ(a/2)=2Γ(a/2+2)/(a(a+2))`. The numerator is uniformly bounded on a fixed
positive real strip; comparison with `|a|⁻²` and the complete squared-resolvent
bound gives `Σρ|½Γ((ρ−s)/2)|=O_δ(1+log Im s)`.
Outside `F`, `Re(ρ−s)≤θ−σ`, so each damped mode has the additional factor
at most `y^((σ−θ)/2)`. Combine with the full finite-part estimate and split
the absolutely convergent divisor sum at `F`.

This is an infinite-tail theorem in the actual finite-layer world. It
removes the infinite counterterm, but still leaves the finite exceptional modes.
At inverse-height damping these modes vanish by
`euler-fe-counterterm-free-high-gaussian-passage.md`. No replication or
contradiction is claimed.

Formalization: `EulerFETransportTheory/OnlyExceptionalGaussianModesRemain.lean`.

## Lean declarations and audit

- `exists_gaussianMode_unit_bound`: uniform squared-resolvent majorant for Gamma amplitudes.
- `exists_finiteGaussianFinitePartError_bound`: finite exceptional subtraction estimate.
- `tendstoUniformlyOn_finiteGaussianFinitePartError`: the full high-strip weighted limit.
- `not_asymptoticAbscissaLaw_has_finiteGaussianControl`: actual `¬AAL` specialization.

Direct `lake --old env lean` checking passes. All four transitive axiom audits
contain only `propext`, `Classical.choice`, and `Quot.sound`.
