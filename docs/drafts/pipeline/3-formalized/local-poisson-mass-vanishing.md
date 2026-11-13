# Local Poisson mass from radial convergence

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** Supporting analytic input for critical-state cyclicity; no separate contribution count.
- **Statement:** If a finite angular measure represents `u` by the disk Poisson kernel, bounded radial values tending to zero almost everywhere on an arc force zero representing mass on every smaller arc.

## Proof

Write `δ=1-r>0`. For `t∈[α,β]`, the interval `[t-δ,t+δ]` lies in `[α-η,β+η]` when `δ≤η`. Chord length is bounded by angular distance, so on that interval the Poisson kernel is at least `(1+r)/(4δ)`. Its angular integral is therefore at least `(1+r)/2≥1/2`.

Integrate over `t∈[α,β]`, apply Fubini, and enlarge the positive measure integral to all angles. The representation gives

`ν([α,β]) ≤ 2 ∫_[α-η,β+η] u(r exp(iθ)) dθ`.

At a fixed radius below one, continuity and a global bound for the kernel justify product integrability against finite restricted measures. For radii tending to one, a common bound on the larger arc and almost-everywhere convergence to zero make its integral tend to zero by dominated convergence. The displayed estimate then forces `ν([α,β])=0`.

## Formalization

Final plain source check passed with exactly `propext`, `Classical.choice`, and `Quot.sound`. Module wired into `HTGeometry.lean`; no umbrella build.

Module: `GaloisForLFunctions/HTGeometry/HardyBoundary/LocalPoissonMassVanishing.lean`.

- `measureReal_Icc_le_two_mul_radial_integral`
- `measureReal_Icc_eq_zero_of_bounded_radial_ae_vanishing`
