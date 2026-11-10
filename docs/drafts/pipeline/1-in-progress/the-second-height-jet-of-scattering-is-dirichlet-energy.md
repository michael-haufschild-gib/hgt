# The second height jet of scattering is Dirichlet energy

- **ID:** the-second-height-jet-of-scattering-is-dirichlet-energy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: recover physical differential energy from the intrinsic geometric diagonal.

## Target

For every physical L² state, prove the extended limit

`N² ∫₀∞ exp(−Nt) archLevyDensity(t) ‖U_t f−f‖² dt`
`→ ½ ∫ℝ (2πξ)² |Fourier(f)(ξ)|² dξ`,

including infinity. Thus the finite second-height limit occurs exactly at
the Fourier H¹ threshold. Identify this limit with the actual raw scattering
tower defect, after the exact geometric Robin mass drift is removed, on the
complete Weil form domain. For smooth sources the limit must be half the
physical derivative norm squared.

## Mechanism

The finite tower kernel is `(1−exp(−Nt))ω(t)`. Its omitted tail concentrates
at `t≈1/N`; `tω(t)→½`. Fourier translation converts the squared increment
to `2(1−cos(2πξt))`, whose quadratic jet yields the Dirichlet multiplier.
A uniform quadratic-frequency bound gives dominated convergence at finite
Dirichlet energy; Fatou forces divergence outside it. The finite-aperture
prime correction decays exponentially and disappears after multiplication
by `N²`.

The raw tower identification and the H¹ classification are part of the
target. A scalar Laplace asymptotic alone would not complete it.

## Boundary

This concerns regularity of the geometric diagonal, with its existing
normalization. It assumes neither unshifted positivity nor invariant
torus gluing. The conjecture is not yet formalized.

## Exact proposed law

Write `n=N+1`, `J` for the physical form embedding, `b_n` for the exact
scattering mass coefficient, and `E_n` for the finite geometric form. Then

`n² [Re W(u,u) − E_n(Ju) + (b_n−2 gammaHardyPhaseRate(0))‖Ju‖²]`
`= T_n(Ju) − Σ_{2≤k≤exp(2a)} n² k^(−n) Λ(k) Re⟨P_k Ju,Ju⟩`,

where `T_n(f)=n²∫₀∞e^(−nt)ω(t)‖U_t f−f‖²dt`. The finite sum tends to zero.
Under Fourier transform the multiplier of `T_n` is

`φ_n(τ)=∫₀∞ e^(−x) [(x/n)ω(x/n)] τ²x sinc²(τx/(2n)) dx`.

The corpus's global bounds on `ω` give `0≤φ_n(τ)≤τ²` and
`φ_n(τ)→τ²/2`. Tonelli transfers the identity to every physical L² state.
Dominated convergence proves the finite-energy limit; Fatou proves the
infinite-energy limit. Consequently existence of a finite renormalized
second-height limit is equivalent to `Ju∈H¹`. Plancherel identifies the
smooth-source coefficient as `½∫|u′|²`.

## Formalization boundary

Scalar multiplier identity, uniform bound, and limit checked in Lean.
The full L², H¹, finite-prime, and raw-source proofs are drafted; verification
is pending. This card remains in progress until all parts pass.
