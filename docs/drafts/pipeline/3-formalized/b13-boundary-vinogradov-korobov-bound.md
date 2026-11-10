# An independent zero-free bound at boundary damping angles

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Fix `σ<1`, a finite filter packet `F`, selected point `ρ`, and centre `β`.
Put `d=1+#{q∈F:ρq≠ρ}`, `φ(t)=−π/2+1/t`, and
`w(T)=(log T)^(−2/3)(log log T)^(−5/3)/10^8`.
There are `C>0,N` such that, eventually in `t`, simultaneously for
`0<a≤t/4` and `0≤h≤1`, the literal rotated prime filter satisfies

`|A_h^rot(t)|≤C h^d t^N exp(a(1−σ)t/2−a t w(t³+1)/4)`.

Constants and the height threshold are independent of `a,h`.
No assumption about the exceptional layer or the remainder divisor enters.

For fixed `a>0`, the width saving dominates every polynomial. Thus
`h(t)=exp(−κt)` forces raw decay when `dκ≥a(1−σ)/2`, including equality.
More generally, eventual `0≤h(t)≤1` and

`h(t)^d≤exp(−a(1−σ)t/2+a t w(t³+1)/8)`

force decay. In particular the enlarged spacing

`h(t)=exp((−a(1−σ)/2+a w(t³+1)/8)t/d)`

still makes the complete literal prime filter tend to zero.

## Proof

Use the absolute Euler line `r=9/8` and a rectangle of total zeta height
`H=t³`. The actual uniform pole-subtracted logarithmic-derivative theorem
covers its full interior down to `c=1−w(H+1)/2`, including bounded heights.
The filter kills the pole residue exactly; zero-freeness removes every
zero residue. Eventually `σ<c`, so no Gamma pole is crossed.

On a fixed positive Mellin strip, the boundary kernel with any polynomial
vertical weight is bounded by

`C t^N y^(−x/2) exp(−|v|/(4t))`.

Rescale the vertical coordinate by `t` and absorb its polynomial factors
into half the angular decay. The complete filter estimate preserves `h^d`.
After translation by the observation height, the same exponential envelope
holds with a constant factor. On the rectangle boundary the logarithmic
derivative costs at most `D(1+H)^4`.

The left edge contributes `O(h^d t^N exp(at(c−σ)/2))`. The horizontal
edges and truncated Euler tails have the additional decay `exp(−t²/8)`.
Since `r−c≤1` and `4a≤t`, this absorbs the difference between the Euler
and shifted real exponents, uniformly in `a`. Exact literal-prime inversion
then yields the displayed bound.

Finally `w(t³+1)⁻¹≪(log t)^3`, so `t^n exp(−b t w(t³+1))→0` for every
`n` and `b>0`. Combining this with the spacing bound proves all decay laws.

## Lean declarations

`ExceptionalLayerTheory/BoundaryZeroFreeContours.lean` proves the weighted
kernel envelope, the full zero-free rectangle, exact pole cancellation and
literal-prime inversion. Its direct source audit passes without warnings;
all five printed transitive audits contain only standard Lean axioms.

`ExceptionalLayerTheory/VinogradovKorobovBoundsForBoundaryDamping.lean` contains:

- `exists_boundaryPrimeDampingFilter_uniform_vinogradovKorobov_bound`;
- `exists_boundaryPrimeDampingFilter_vinogradovKorobov_bound`;
- `tendsto_polynomial_mul_exp_neg_boundary_vk_width`;
- `tendsto_boundary_prime_filter_zero_of_vk_relaxed_contraction`;
- `tendsto_boundary_prime_filter_zero_of_critical_contraction`;
- `tendsto_boundary_prime_filter_zero_of_vk_schedule`.

Its final direct source audit passes without warnings. Across both modules, all eleven printed
transitive dependency lists contain only `propext`, `Classical.choice`,
and `Quot.sound`. Both modules are imported by the exceptional-layer umbrella.

## Remaining gap

The exceptional signal has rate `a(Re ρ−σ)/2`; the independent upper
estimate retains rate `a(1−σ)/2`. The saving is subexponential, leaving
`a(1−Re ρ)/2>0`. Raw decay at critical contraction is compatible with
nonzero normalized divisor recovery. No B13 exclusion follows.
