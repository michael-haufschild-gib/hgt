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

The contour identity and this error estimate are formalized and pass direct
source audit. The normalized divisor limit still awaits its source audit.
The independent Euler upper rate remains `a(1−σ)/2`, so even the proposed
receiver leaves arithmetic gap `a(1−Re ρ)/2`.

## Derivation

The rotated weight is an entire exponential multiplier of the real-damping
weight. The same finite residue rectangle therefore cancels the pole and
every unwanted zero exactly. On horizontal edges the sharp Gamma estimate
leaves angular margin `δ=π/4−|φ|/2>0`; its polynomial factors are dominated
by `exp(−δT)` as the rectangle height tends to infinity.

The regular vertical integral has the full spacing factor and one weighted
kernel moment. At angle `−π/2+1/t`, the proved moment estimate costs only
polynomial height. Consequently its complete error is bounded by
`C h^d t^N exp(at(c−σ)/2)`. The reciprocal selected mode has bound
`D t^M exp(−a(Re ρ−σ)t/2)`. Dividing cancels `h^d` exactly and leaves
`CD t^(N+M) exp(−a(Re ρ−c)t/2)→0` for every `a>0`.

For `h=exp(−κt)`, the predicted literal prime growth range is
`dκ<a(Re ρ−σ)/2`. Independent arithmetic decay holds above
`dκ>a(1−σ)/2`. The fixed Gamma gap disappears; the arithmetic gap remains.

## Lean target

- `RotatedContoursForFiniteDivisorFilters.lean`: rotated residue identity,
  horizontal decay, full boundary-angle remainder estimate.
- `BoundaryDampingReadsTheDivisor.lean`: arbitrary-contraction recovery at
  every positive speed, actual-divisor capstone, and literal growth/decay ranges.

`RotatedContoursForFiniteDivisorFilters.lean` passes direct source audit
without warnings; all six transitive dependency lists contain only
`propext`, `Classical.choice`, and `Quot.sound`.
The divisor-limit module remains unaudited.

## Available inputs

- `ComplexGaussianDamping.lean`: exact literal-prime Mellin identity,
  boundary kernel moments, independent arithmetic bound, mode growth.
- `ContourBoundsForFiniteDivisorFilters.lean`: weighted zeta residue
  rectangle, actual finite-layer regular-line bounds, real-damping receiver.
- `ArbitraryDampingContractionReadsTheDivisor.lean`: arbitrary-contraction
  normalization and the actual-divisor limit for real damping.
