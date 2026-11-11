# Exponential blocks with self-consistent interpolation weights

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A89, prescribed `R(T)=o(log T)`.

For distinct nodes `z_j`, let
`c_j(z)=∏_{k≠j} (−z_k)/(z_j−z_k)` be the Lagrange weights at zero.
Seek conjugate-paired nodes near a separated imaginary grid satisfying

`exp(T z_j)=c_j(z)`.

Then `Σ_j exp((T+v)z_j)=Σ_j c_j(z)exp(vz_j)` is the interpolation
of the exponential at zero. A contour remainder bounds its difference
from `1` by `exp(8Γ|v|)3^(−M)` for `M` nodes in `|z|≤2Γ`.
Taking `M≥16Γ(R+8)` would give a positive block throughout the window.

The proposed construction solves
`z_j=(2π i k_j+log c_j(z))/T` by contraction. Define each logarithm
through its individual numerator and denominator factors near the grid;
this avoids a branch cut for negative interpolation weights. Logarithmic
derivatives involve reciprocal node spacings, not the exponentially large
weights. With spacing comparable to `1/R`, coarse bounds are
`O(MR/T)` for the contraction and `O(M log M/T)` for node displacement.
For `Γ=T^(1/4)` and `R=o(log T)`, these vanish; the local node density
`O(R)` also fits a logarithmic zero-count bound.

## Quantitative route

On a product of disks of radius `s/8` about nodes of minimum separation
`s`, expand `log c_j` as a sum of logarithms of individual factors.
Their arguments stay within `1/4` of `1`. A sufficient contraction bound
is `6M/(sT)≤1/2`; a sufficient self-map bound is
`(M log(4Γ/s)+π)/T≤s/16`. Both hold for `M≈ΓR`, `s≈1/R`,
`Γ=T^(1/4)` and `R=o(log T)`. Construct the upper-half-plane nodes first and append their conjugates;
this supplies symmetry without imposing it on the fixed-point map.

The contour remainder can instead be replaced by the existing exponential
Taylor remainder and exact polynomial interpolation. For ordered separated
nodes, the factorial denominator in each Lagrange weight bounds their total
mass exponentially in `M`; choosing a larger fixed constant in `M≈ΓR`
then makes the Taylor tail negligible.

## Configuration assembly

Append the conjugate nodes and reflect their depths. A common positive
depth multiplies the interpolated trace by a positive exponential; the
reflected negative-depth terms are negligible at the chosen centre.
Positivity on the enlarged window must survive convolution with the
nonnegative spline kernel of support `[-8,8]`. Choose successive common
depths strictly increasing to the unattained top. Earlier blocks then
have a strict exponential deficit; later blocks have summable spline
tails by taking their frequencies sufficiently large.

## Missing proof

Uniform constants, conjugate symmetry, the contour remainder and the
configuration assembly remain unproved. In particular, the construction
must preserve the exact identity above after node displacement; treating
the weights as fixed would reintroduce the exponential phase-error cost.
`TheLogarithmsOfInterpolationWeightsAreStable.lean` contains an unchecked
proof draft of the exact exponential change-of-weights identity and the
`6M/s` Lipschitz estimate.
`TheInterpolationWeightsCanBeExponentialCoefficients.lean` contains an
unchecked contraction proof with explicit separation and displacement
bounds. `TheInterpolationWeightsAdmitNearbyLogarithms.lean` supplies those data
from explicit geometric inequalities.
`TheCalibratedExponentialBlockApproximatesAConstant.lean` bounds the error by
`((2B/δ)^k/k!) ((RB)^(k+1)/(k+1)!) exp(RB)` for `k+1` calibrated nodes.
All four drafts are unchecked. Discharging the scalar bounds on a growing
grid and assembling the configuration remain unfinished.
