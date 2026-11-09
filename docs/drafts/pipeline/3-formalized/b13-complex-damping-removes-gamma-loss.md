# Complex damping removes the fixed Gaussian Gamma loss

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

At damping `exp(−at) exp(iφ(t))`, `φ(t)=−π/2+1/t`, the complete literal
prime filter satisfies

`|A_h^rot(t)| ≤ C h^d t^N exp(at(c−σ)/2)`

for every `c>max(1,σ)`, uniformly in `0≤h≤1`, `t≥1`, and real `a`.
No finite-layer hypothesis enters. The individual kernel mode at `ρ`
has norm tending to infinity whenever `a(Re ρ−σ)>0`; its previous fixed
`π/4` Gamma penalty is absent.

## Proof

Rotation multiplies the Mellin kernel by `exp(−iφw/2)`. For
`w=ρ−σ−it`, its modulus changes by `exp(φ(Im ρ−t)/2)`. Existing two-sided
Gamma bounds therefore give opposite exponential envelopes with rate
`a(Re ρ−σ)/2−π/4−φ/2`, uniformly for `|φ|≤π/2`. The explicit angle makes
the height exponent `a(Re ρ−σ)t/2−1/2`.

Complex Mellin inversion identifies the rotated Euler integral with the
literal Gaussian prime sum. The finite filter's polynomial multiplier
retains all `d` spacing factors. On a positive Mellin line the kernel has
majorant `B(1+|v|)^N exp(−(π/4−|φ|/2)|v|)`. At angular margin `1/t`,
rescaling `v=tu` bounds every weighted kernel moment by a polynomial in `t`.
The resulting Euler bound has no additional fixed exponential cost.

## Lean proof

`ExceptionalLayerTheory/ComplexGaussianDamping.lean`:

- `exists_rotatedGaussianMode_exponential_bounds`
- `tendsto_norm_boundaryGaussianMode_atTop`
- `rotatedPrimeDampingFilter_eq_euler_integral`
- `exists_rotatedGaussianKernel_boundary_moment_bound`
- `exists_boundaryPrimeDampingFilter_arithmetic_bound`

Direct source audit passes without warnings. All five transitive dependency
lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
The module is imported by the exceptional-layer umbrella.

## Remaining receiver

Mode growth alone does not recover a zero from the prime sum. The rotated
finite-layer contour identity remains open; see
`../1-in-progress/b13-boundary-damping-recovers-exceptional-divisor.md`.
Even the proposed receiver leaves arithmetic gap `a(1−Re ρ)/2`.
