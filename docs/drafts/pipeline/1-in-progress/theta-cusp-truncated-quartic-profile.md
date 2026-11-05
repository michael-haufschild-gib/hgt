# Quartic flux truncated at its double zero

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** Positive definiteness of the truncated fifth even repair for every
  `x≥0`, and of its literal weighted source for `0<a<1/2`, `r>0`.
  The flux profile is `P₊(r)=max(1−r²/2,0)²`.

The untruncated quartic fails at theta scale thirty-two, beyond its double
zero. Truncation removes that branch. The profile is continuously
differentiable: both its value and derivative vanish at `r²=2`.
On `r≥0` its flux is compactly supported, vanishes at both endpoints, and
has zero integrated derivative. Every mixed entry is preserved. These
identities, continuous differentiability, and strict positivity for
`r≥√2` are formalized in `FifthEvenTruncatedQuarticFlux.lean`; see
[the formalized result](../3-formalized/truncated-quartic-flux-preserves-fifth-even-matrix.md).

At `R=√2`, the polynomial tail identity gives
`∫_(R,∞) (P·flux)' = −P(R)flux(R)=0`. Deleting this tail derivative
therefore preserves every mixed entry directly. Below `R` the source is
the original quartic repair; above `R` it is native. The derivative also
vanishes at `R`, so both descriptions agree there.

For `x²<1/2`, its aperture-independent correction equals the original
`G_P=(1−2x²)²G−8x²(1−2x²)F²`. For `x²≥1/2`, it vanishes, leaving the
native matrix, already proved PD once `π exp(2x)≥5`.

The complete native reserve `H−(3/20)Kq⁴B ≻ 0` is now formalized for
`q≥7`. Combined with the scalar correction bound, it proves the literal
truncated weighted source positive for every `a>0`, `π exp(r)≥7`; see
[the formalized upper ray](../3-formalized/theta-cusp-quartic-cross-load-ray.md).
The original quartic repair is also positive on an origin neighborhood.

**Unproved input:** an unconditional lower bound for the complete profiled
matrix on the remaining interval `π≤q<7`, retaining all theta atoms.
The proved origin neighborhood has no bound covering this interval.
Rank-nine integrated sign remains open.

## Scalar comparison

For `q≥5`, `x²≤1/2`, the complete-source bound is
`G_P(x)>−(3/20)K(x)q⁴`. Before scale five, `G_P≥F²/16`; before
scale `37/10`, the stronger `G_P≥2F²` holds. Affine center bounds also
give explicit polynomial reserves below five and a sharper negative
allowance on `[5,7]`, retaining the complete source and derivative errors.

All seven scalar statements are formalized in
`FifthEvenPolynomialCrossCompactEnvelope.lean`; see
[the interval reserves](../3-formalized/quartic-theta-compensation-interval-reserves.md).
The matrix comparison below scale seven remains unproved.

## Lower-interval remainder

The existing Gaussian remainder allowance requires `q≥5`. Retaining the
fourth atom suggests the all-order Cauchy bound
`|J_n−J_n^(4)|≤n!·20000 f₁² exp(−431q/25)/(3/20)^n` for `q≥3`.
On the complex disk, the tail starts at atom five: its Gaussian majorant is
`626 exp(−25a)`, `a=37q/50`; pairing with the full source gives
`20000 exp(−26a)` before restoring the first-atom normalization.
This bound and the resulting compact matrix sign remain unformalized.
