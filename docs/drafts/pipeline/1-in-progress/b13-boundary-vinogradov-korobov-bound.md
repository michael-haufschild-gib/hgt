# An independent zero-free bound at boundary damping angles

- **Obstacle:** B13.
- **Stage:** 1-in-progress
- **Type:** CONJECTURE

## Target

For `σ<1`, `a>0`, `φ(t)=−π/2+1/t`, and the actual pole-and-divisor
filter of degree `d`, prove uniformly over `0≤h≤1` that

`|A_h^rot(t)|≤C h^d t^N exp(a(1−σ)t/2−a t w(t³+1)/4)`

eventually, where `w` is the corpus's actual Vinogradov–Korobov width.
No finite exceptional-layer assumption may enter the bound.
The saving should force decay at the absolute contraction threshold and
permit spacing enlarged by a positive multiple of `w(t³+1)`.

## Derivation to formalize

Shift the Euler line to `1−w(t³+1)/2` inside a rectangle with total zeta
height `t³`. The existing uniform pole-subtracted logarithmic-derivative
bound covers this entire rectangle, including bounded heights. The filter
kills the pole residue exactly; the zero-free region removes all zero
residues. Positive Mellin real parts prevent Gamma poles.

Boundary rotation gives kernel decay `exp(−|v−t|/(2t))`. Absorb polynomial
vertical factors into half that decay, preserving every `h` factor. A
height-`t³` rectangle then has horizontal and Euler-tail errors with
quadratic exponential decay, dominated by the shifted main bound.

## Inputs and limits

- `Sieve.exists_bound_zetaLogDerivReg_vk_uniform`: full zero-free rectangle
  and a uniform bound for the pole-subtracted logarithmic derivative.
- `RotatedContoursForFiniteDivisorFilters.lean`: analytic rotated weight
  and exact weighted zeta residue identity.
- `ComplexGaussianDamping.lean`: literal-prime inversion and angular bounds.
- `VinogradovKorobovBoundsForDampingFilters.lean`: actual width asymptotics.

The proposed saving is subexponential. Even if proved, it leaves the fixed
gap `a(1−β)/2` to the exceptional-layer signal; it is not B13 exclusion.

## Lean status

`BoundaryZeroFreeContours.lean` passes direct source audit without warnings.
Its weighted kernel estimate, full zero-free rectangle, pole cancellation
and literal-prime inversion have standard-axiom-only transitive audits.
`VinogradovKorobovBoundsForBoundaryDamping.lean` contains the upper bound,
critical decay and relaxed-contraction proofs; its direct audit is pending.
