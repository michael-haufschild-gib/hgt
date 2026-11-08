# Exact seventh-order aliasing of integer spline differences

- **ID:** alias-notch-saturation-for-differentiated-splines
- **Stage:** 1-in-progress
- **Type:** THEOREM (formalization in progress)
- **Statement:** Increasing harmonic-zero multiplicity while retaining a fourth-power Fourier denominator leaves an exact seventh-order notch in the complete alias sum, also for explicit profiles of integral one.

## Exact families

Let `B_m` be the centered convolution of `m` unit interval densities,
`g_n = Δ^n B_4`, and `Δf(u)=f(u)-f(u-1)`. Put
`a_f(s)=Σ_{k≥1}|f̂(2πks)|²` and `M_f=∫f²`.
All these profiles are real, compactly supported and `C²`.
For `n≥1`, `∫g_n=0` and `M_g>0`. For integers `j≥0`,

`a_g(j+ε)=M_g ε^7/(2(j+ε)^8)`, whenever `0<ε<1/(2(n+2))`.

For `r≥0`, set `n=2r+1`, `m=2r+5`, and
`φ_r(u)=B_m(u)+g_n(u+n/2)`. Then `∫φ_r=1` and

`|φ̂_r(2πt)|²=[1+(2πt)^(4r+2)] |B̂_m(2πt)|²`.

Writing `s=j+ε`, for `0<ε<1/(8r+8)` the exact law is

`a_φ(s)=M_g ε^7/(2s^8)+(ε/s)^(4r+10)(M_B/(2ε)−1/2)`.

For every positive integer `j`, both normalized alias sums tend to
`M_g/(2j^8)>0` after division by `ε^7` as `ε→0+`.

## Proof

The Fourier convention is `f̂(z)=∫f(u)exp(izu)du`. Translation gives
`ĝ_n(z)=(1−exp(iz))^n B̂_4(z)` and

`z^4 ĝ_n(z)=(1−exp(iz))^n(exp(iz)−1)^4/exp(2iz)`.

Thus the eighth-power weighted squared spectrum is integer-periodic.
Termwise scaling and summation give
`a_g(j+ε)=(ε/(j+ε))^8 a_g(ε)`.
For any real compact `C²` profile supported in `[-A,A]`, Poisson summation
of its autocorrelation gives

`a_f(ε)=M_f/(2ε)−(∫f)^2/2` when `0<ε` and `2A<1/ε`.

Applying this with `A=n+2` proves the difference formula. Its square mass
is positive because its Fourier transform at `i` is nonzero.
The centered odd difference and even cardinal spline have orthogonal
Fourier values on the real axis. Their squared spectra add. The cardinal
weighted spectrum has exponent `2m`; the same Poisson identity, now with
mean one, gives the displayed unit-integral formula and positive limit.

## Mathematical scope

The full harmonic sum retains seventh-order mass even as the displayed
Fourier factorization inserts arbitrarily many individual harmonic zeros.
This supplies the positive survivor of the failed inference from individual
zero multiplicity to alias-notch order. It does not establish arithmetic
matrix positivity, a negative zeta test, or AAL.

## Lean status

Namespace: `ArithmeticHodgeTheoryOfDegenerations.SplineAliasNotches`.

- `TheAliasNotchOrderIsSetByTheSpectralTail.lean`: checked exact scaling,
  general below-spacing Poisson law, positive square mass, exact difference
  formula and normalized limit. Four audited capstones use only
  `propext`, `Classical.choice`, `Quot.sound`; final source audit pending.
- `UnitMassProfilesRetainTheSeventhOrderAliasNotch.lean`: mean one, even/odd
  spectrum decomposition, cardinal multiplier, exact alias law and positive
  normalized limit. Compiler check in progress.
