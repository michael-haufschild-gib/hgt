# Mass-shifted degree-one admitted-kernel positivity

## Claim

On the full prime--Gamma contact window `0 < w² < 41/2`, canonical degree-one shifted-Xi amplitude
`A_w(X)=X-m₁(w²)/m₀(w²)` has strictly positive literal adaptive mixed Gamma kernel at every Euler source point `x ≥ 1`.

## Source mechanism

Global squared-node height separation gives
`(4y+81)m₁(y)<4m₀(y)`, hence
`t=yr(y)<4y/(4y+81)`. Throughout `y<41/2`, this is below `7/12`.
For `z=w log x ≥ 0`, monic affine-kernel bracket is
`24t²B₂(z)-12tB₃(z)+B₄(z)`. Exact identity
`B₄(z)-7B₃(z)=z²(z²+3z+3)≥0` makes bracket strictly positive.

## Significance

First nontrivial admission-sensitive positive law for actual common arithmetic kernel. Explains why arbitrary positive-root monic amplitudes can be negative while source-selected first-face amplitude is safe. Does not yet prove Lebesgue-plus-Archimedean domination over von Mangoldt formation.

## Proof obligations

1. Prove reverse-Bessel inequality symbolically.
2. Transport exact corpus moment-ratio contraction to dimensionless null root.
3. Prove strict pointwise positivity of literal Gamma-averaged kernel.
4. Formalize unconditionally and wire into `RHTower.lean`.

## Hostile tests

- No flatness assumption smuggled into ratio bound.
- No claim beyond degree one or `w<1`.
- Pointwise kernel positivity is not arithmetic quadrature domination.
- No computation or asymptotic evidence.

## Status

Formalized unconditionally in
`XiShiftedAdaptiveDegreeOneAdmittedKernelPositivity.lean`.

No singular-face hypothesis is required for kernel positivity: source moment ratio itself obeys
global safe-cone bound. Consequently theorem applies whenever canonical degree-one polynomial
becomes actual admitted null polynomial anywhere in prime--Gamma contact window. Remaining gate is
arithmetic formation comparison, not kernel sign. Earlier `w<1` theorem remains as a sharper
`4/85` subwindow corollary.

Lean also closes incidence explicitly: at flat first minor, vector `(-m₁/m₀,1)` is literally
killed by shifted 2-by-2 Hankel block, and both its raw and monic finite-Hankel polynomials equal
`X-m₁/m₀`.
