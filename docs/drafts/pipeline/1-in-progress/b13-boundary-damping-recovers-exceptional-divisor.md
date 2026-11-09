# Boundary damping and exceptional-divisor recovery

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Statement

For a finite exceptional packet above a complementary abscissa `θ`, choose
`θ<σ<c<Re ρ`, with `c` avoiding the finite packet's real parts. At angle
`φ(t)=−π/2+1/t`, every `a>0` and every eventually positive `h(t)→0` should give

`A_h^rot(t)/(h(t)^d Kφ(exp(−at),ρ−σ−it))
 → −mρ(ρ−1)Π_{q∈F,ρq≠ρ}(ρ−ρq)`.

Unlike the real Gaussian receiver, this conjecture has no fixed positive
threshold on `a(Re ρ−σ)`. The complete complementary divisor must be retained.

## Missing proof

Shift the rotated Euler contour to `c`. The pole and unwanted exceptional
modes are annihilated by the existing exact polynomial multiplier. Prove
horizontal-edge decay for every interior angle and a uniform boundary error
`O(h^d t^N exp(at(c−σ)/2))`. The proved reciprocal-mode bound then gives
exponential separation `a(Re ρ−c)/2` after normalization.

The contour identity and this error estimate are not yet formalized.
The independent Euler upper rate remains `a(1−σ)/2`, so even the proposed
receiver leaves arithmetic gap `a(1−Re ρ)/2`.

## Available inputs

- `ComplexGaussianDamping.lean`: exact literal-prime Mellin identity,
  boundary kernel moments, independent arithmetic bound, mode growth.
- `ContourBoundsForFiniteDivisorFilters.lean`: weighted zeta residue
  rectangle, actual finite-layer regular-line bounds, real-damping receiver.
- `ArbitraryDampingContractionReadsTheDivisor.lean`: arbitrary-contraction
  normalization and the actual-divisor limit for real damping.
