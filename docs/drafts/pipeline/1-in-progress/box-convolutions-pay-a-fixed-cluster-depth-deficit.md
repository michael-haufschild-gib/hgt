# Box convolutions pay a fixed cluster depth deficit

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** Exterior mass in the Turán cluster receiver; M7/A78.
- **Status:** Camera Fourier bound checked. Mass, uniform Lorentzian envelope,
  full deep/shallow exterior bound, and Turán receiver written; checks pending.

## Proposed estimate

Let `Bₙ=boxPlateau A h (n+1) r`, with `A,h,r>0`,
`δ=A+(n+1)h+r`, and `b=zetaZeroWidth`. For a zero `ρ`, put
`z=γ(ρ)-t+ib` and `Kₙ(ρ)=exp(iyz) B̂ₙ(z)`. Assume `y≥δ`.
Every zero has `Im z≥0`, so centering removes exponential amplification.

If exterior zeros with depth at least `b-d` have ordinate gap `g>0`,
the proposed complete multiplicity-weighted exterior norm bound is

`[(2/h)(1+g⁻²)(hg)⁻ⁿ + (4A+4/h)exp(-d(y-δ))] lorentzMass(t)`.

For `hg>1`, the first term decays exponentially in convolution order.
Reserve one box factor for the summable `1/|z|²` envelope; the other
`n` factors each cost at most `1/(hg)`. The all-frequency envelope follows
by combining the mass bound `2A` with the reserved-factor bound `2/(h|z|²)`.

## Turán consequence to prove

The profile has mass `2A` and support `[-δ,δ]`. A sector cluster containing
a zero of depth at least `b-ε` should have finite signal at least
`A κ exp(-ε(y_max+δ))`. Choose convolution order proportional to `log T`.
The full exterior is smaller than that signal whenever

`n log(hg)-ε(y_max+δ)` and `d(y_min-δ)-ε(y_max+δ)`

grow as positive multiples of `log T`. Thus a fixed positive depth deficit
can replace the existing `E/log T` deficit. The deep ordinate gap remains;
this conjecture does not establish it for arbitrary clusters.

The primary exterior-unconditional formulation should be: every such
sector cluster is visible at that level, or has another zero outside it
with depth at least `b-d` and ordinate distance less than `g`.

## Corpus connections

- `RHTower/BoxConvolutionPlateau`: actual smooth profiles, support,
  convolution transform, and `norm_paperFT_boxPlateau_le`.
- `MultiscaleMollifiedZetaField/TheDepthCenteredCameraPaysItsExteriorMass`:
  actual-width centering, shallow/deep split, and full Lorentzian mass.
- `TheWidthCenteredCameraSeesNearTopClusters`: finite Turán receiver.
- `EveryCompactProfileHasSubexponentialConductorFloors`: a fixed profile
  cannot provide the required exponential tail; the profile must vary.

The uniform Lorentzian envelope also pays the gamma remainder directly,
using the existing `exists_norm_gamma_lorentz_le` at unit scale. This costs
`O(log t)` with a constant independent of convolution order. The pole
terms use the same bound and `exp(y+δ)≤t`. No derivative estimates are
needed for this receiver. The profile has supremum at most `δ` after
rescaling, so the existing prime mean-square bound costs `O(T(log T)²)`
when `δ=c log T`, retaining the depth-centering exponential gain.

Written capstone: `BoxCamerasPayFixedDepthDeficits` selects a fixed positive
`η` and lags `ν(h+2)(n+1)`, `1≤ν≤N`. For logarithmic heights bounded by
`L(n+1)`, every eligible cluster has at least half its Turán signal in the
full field, or a deep exterior companion within `g`. The relative exterior
ratios are `exp(ηb)/(hg)` and `exp(ηb-da)`, both strictly below one.

Remaining formalization: verify the written envelope/receiver/rate chain
and the uniform prime/remainder bounds.
