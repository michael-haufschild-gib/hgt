# Positive quartet kernels have logarithmic moment growth

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

For every first-quadrant Xi zero `a`, there are `C>0` and a continuous,
strictly positive, even real kernel `k` with all absolute exponential moments,
such that

`∫exp(s|x|)k(x)dx ≤ C exp((s+6)log(s+6))` for every `s≥0`.

Its Fourier transform is nonzero at every member of `{±a,±conj(a)}` and
vanishes at every other Xi zero. Full multiplicities are included; neither
simple zeros nor a zero of maximal depth is assumed.

## Proof

The existing theorem `RHTower.quartet_seed_transfer` supplies
`k=θ+εu>0`, where `u=quartetSource a`, `|u|≤C_u θ`, and
`û(z)P(z)=z² XiC(z)` for the full quartet divisor `P`.
The perturbed transform satisfies `k̂(z)P(z)=XiC(z)(P(z)+εz²)`, with
exactly the stated behavior at Xi zeros. It is even and bounded in absolute value by
`(1+ε|C_u|)θ`.

First-atom domination and theta reflection give
`θ(x)≤C₀ exp(9|x|/2−π exp(2|x|))`. For `a≥1`, `t≥0`,

`at−exp(2t)≤a log a`.

Below `log a`, discard the negative term; above it, use `exp(t)≥a`
and `exp(t)≥t`. Apply this with `a=s+6`, leaving `exp(-|x|)` as an
integrable majorant. Its integral is `2`, giving the theta moment bound.
Theta domination transfers that bound to the positive quartet kernel.

## Lean

Namespace `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`:

- `ThetaLogMoment.lean`: `exists_theta_double_exp_envelope`,
  `exists_theta_logarithmic_moment_bound`.
- `QuartetLogMoments.lean`: `exists_positive_quartet_log_moments`.

Capstone axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
The positive quartet deformation is existing corpus work; the new result is
its explicit logarithmic moment bound. No external novelty claim.

This supplies the kernel estimate for logarithmic-window localization.
`ZetaLogarithmicWindows.zeta_re_le_of_logarithmic_windows` now proves
continuous exact-depth detection at radius `16log(T+2)`, with only the
standard three axioms. `PrimeLogarithmicWindows.lean` proves the prime
criterion at radius `32log(T+2)` with the same axiom audit; the arithmetic
Stepanov inequality remains open.
