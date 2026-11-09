# Logarithmic prime windows determine zeta width

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** Actual zeta; the arithmetic Stepanov estimate remains open.

## Statement

Let `P=primeWindow`, `A=archPoleWindow` for the fixed cubic-spline trace,
and put `R(T)=32log(T+2)`. For every `α≥0`, the following are equivalent:

1. Every nontrivial zeta zero satisfies `Re ρ≤1/2+α`.
2. There is a fixed `K` such that arbitrarily large centers `T` satisfy
   `P(p)≤A(p)+Kp^α` at every prime with `|log p−T|≤R(T)`.
3. The same windows satisfy an absolute bound of exponent `α` on the trace
   `2 Re lagStructure(log p)=2(A(p)−P(p))`, for some fixed constant.

Centers may be arbitrarily sparse. Setting `α=0` gives an RH equivalence.
Existence of some `0≤α<1/2` gives quasi-RH (`zetaZeroAbscissa<1`).
Failure of RH forces a trace below every fixed `−K` in every sufficiently
late such prime window. No deepest zero or simple-zero assumption occurs.

## Proof

The existing `RHTower.quartet_seed_transfer` supplies, for any selected
first-quadrant Xi zero `a`, a strictly positive even kernel `k=θ+εu`.
Its transform is `XiC(z)(P(z)+εz²)/P(z)`, where `P` removes the selected
quartet with full multiplicities. The multiplier survives throughout that
quartet and vanishes at every other Xi zero; moreover `|k|≤Cθ`.

First-atom domination gives `θ(x)≤C exp(9|x|/2−π exp(2|x|))`. The inequality
`at−exp(2t)≤a log a` for `a≥1,t≥0` then yields

`∫exp(s|x|)k(x)dx≤C' exp((s+6)log(s+6))`, `s≥0`.

For a strip trace with coefficient mass `A`, width `D`, and a local lower
bound on radius `8log(T+2)`, the Chernoff parameter `q=T` gives leakage
at most `AC' exp(DB−T)` at every `|t|≤T+B`. Exponential tilting of the
kernel compensates exactly for normalizing the trace by `exp(-αt)`.
Absolute moments justify termwise integration, including arbitrary index
sets via their countable coefficient support.

The filtered trace has finite conjugate-symmetric spectrum and retains
the selected mode. Its bounded-gap negative excursions contradict a local
floor of smaller exponent on arbitrarily late continuous windows of radius
`16log(T+2)`. This proves continuous detection of every depth.

Prime gaps of exponent `2/3` transfer a prime lower bound of exponent `α`
to the interior half-window with exponent `max(α,a−1/3)`, where `a` is the
current zero width. Two reductions from `a=1/2` give the exact width `α`.
The converse follows from the global trace bound at that width. The explicit
formula `trace=2(A−P)` gives the arithmetic formulation by rescaling `K`.

## Lean

Namespace `GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality`:

- `ThetaLogMoment.lean`: `exists_theta_logarithmic_moment_bound`.
- `QuartetLogMoments.lean`: `exists_positive_quartet_log_moments`.
- `PositiveKernelLeakage.lean`: `positive_kernel_logarithmic_floor`.
- `PositiveKernelConvolution.lean`: `integral_kernel_cexp_tsum` and tilt identities.
- `ZetaQuartetFilter.lean`: `exists_zeta_quartet_log_filter`.
- `KernelLogarithmicTrace.lean`: `zeta_kernel_logarithmic_floor`.
- `ZetaLogarithmicWindows.lean`: `zeta_re_le_of_logarithmic_windows`.
- `PrimeLogarithmicWindows.lean`: `zeta_re_le_iff_stepanov_logarithmic_power_windows`,
  `riemannHypothesis_iff_stepanov_logarithmic_windows`,
  `quasiRH_iff_stepanov_logarithmic_power_windows`, and the trace/absolute variants.

All twelve prime-window capstone audits contain only `propext`,
`Classical.choice`, `Quot.sound`. The positive quartet deformation is
existing corpus work. The explicit moment estimate and logarithmic
localization sharpen the previous log-square criterion for actual zeta.
No external novelty claim.

## Remaining boundary

This identifies a smaller decisive sample; it does not produce its
arithmetic upper bound. B130 remains open. The theorem does not settle
bounded-window detection for arbitrary configurations with zeta's zero count.
The exception-tolerant refinement is on
`1-in-progress/power-thin-exceptions-in-logarithmic-prime-windows.md`.
