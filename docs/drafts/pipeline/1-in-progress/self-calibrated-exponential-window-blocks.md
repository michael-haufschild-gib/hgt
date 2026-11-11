# Exponential blocks with self-consistent interpolation weights

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A89, prescribed `R(T)=o(log T)`.

For distinct nodes, put `c_j(z)=∏_{l≠j}(−z_l)/(z_j−z_l)`.
Solve `exp(Tz_j)=c_j(z)` by moving the nodes. Then the literal sum
`Σ_j exp((T+v)z_j)` is the Lagrange interpolation of `exp(vz)` at zero.
Exact self-consistency avoids the exponential error from perturbing fixed
weights after their phases have been chosen.

## Finite block

Normalize every numerator and denominator factor at reference nodes `b`.
Their logarithms stay near `1` on coordinate disks of radius `r`, provided
`8r≤s`, where `s` bounds node norms and separations below. The logarithmic
correction has Lipschitz constant `6M/s`. Thus `12M≤sT` gives contraction.
A phase shift of at most `2π/T` supplies the initial logarithms. If
`‖b_j‖≤B₀`, their real parts have size at most
`2M(|log s|+|log(2B₀)|)`, yielding an explicit self-map inequality.

For `k+1` calibrated nodes with `‖z_j‖≤B` and index separation `δ`,
Taylor interpolation gives error at most

`((2B/δ)^k/k!) ((RB)^(k+1)/(k+1)!) exp(RB)`.

The inequalities `2B/δ≤8k`, `512RB≤k`, `k≥1` make this `≤1/4`, using `e<3`.

Candidate grid: `Γ=T^(1/4)`, `k=ceil(2048Γ(R(T)+8))`,
`b_j=i(Γ+2Γj/k)`, `s=Γ/k`, `r=min(s/8,η)` for a fixed depth tolerance `η>0`.
Perturbation preserves norm bound `B=4Γ` and index separation `δ=s`.
The calibration inequalities follow from `ΓR²log Γ/T→0`;
local node density `O(R)` fits `C log Γ` because `R=o(log T)`.

## Configuration assembly

Take twice the real part and reflect depths, retaining positive ordinates.
A common positive depth supplies exponential growth; reflected negative
terms are negligible. The nonnegative, unit-mass kernel `upow 1 7`,
supported on `[-8,8]`, transfers positivity to the spline trace.
Successive common depths increase strictly to the unattained top. Earlier
blocks have an exponential deficit; later blocks have summable spline tails.

## Lean status and gaps

Six full proof drafts in `SurfaceOfSpecZ/ScaleLocality/`, all unchecked:

- `TheLogarithmsOfInterpolationWeightsAreStable`: exact factor identity and `6M/s` bound.
- `TheInterpolationWeightsCanBeExponentialCoefficients`: contraction with explicit bounds.
- `TheInterpolationWeightsAdmitNearbyLogarithms`: logarithm data from geometric bounds.
- `TheCalibratedExponentialBlockApproximatesAConstant`: factorial interpolation error.
- `TheExponentialInterpolationErrorIsSmallAtDenseGrids`: error `≤1/4`, real part `≥3/4`.
- `TheCalibratedNodesStayOnASeparatedImaginaryGrid`: positive blocks from explicit grid inequalities.

Growing-grid estimates, spline transfer and the full configuration remain unproved.
