# Logarithmic windows through positive quartet deformation

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** B130 scale locality: replace log-square prime windows by `C log(T+2)`.

## Positive quartet isolation — existing corpus theorem

For a first-quadrant Xi zero `a`, let `P` be its full-multiplicity quartet
divisor and `u=quartetSource a`. `ThetaSeedTransferQuartet.quartetSource_spec`
gives a real even smooth source with `|u|≤Cθ` and transform `XiC(z)z²/P(z)`.
The theorem `quartet_seed_transfer` gives, for sufficiently small `ε>0`,

`k=θ+εu>0`, with transform `XiC(z)(P(z)+εz²)/P(z)`.

Its transform is nonzero at every member of the selected quartet and zero
at every other Xi zero. Moreover `|k|≤(1+ε|C|)θ`. No simple-zero or
maximal-depth assumption occurs. This existing deformation supplies the
positive kernel directly; polynomial translation repair is unnecessary here.

## Logarithmic theta moment estimate — formalized

First-atom domination gives `θ(x)≤C exp(9|x|/2−π exp(2|x|))`.
For `a≥1`, `t≥0`, split at `t=log a` to prove
`at−exp(2t)≤a log a`: above that point use `exp(t)≥a` and `exp(t)≥t`.
With `a=s+6`, integration against `exp(-|x|)` yields

`∫exp(s|x|)θ(x)dx≤C' exp((s+6)log(s+6))`, `s≥0`.

Theta domination transfers this bound to `k`. The same kernel therefore
isolates the selected quartet with logarithmic absolute moment growth.
`ScaleLocality.ThetaLogMoment.exists_theta_logarithmic_moment_bound` passes
Lean with only `propext`, `Classical.choice`, `Quot.sound`.
`QuartetLogMoments.exists_positive_quartet_log_moments` proves the quartet
specialization with the same axiom audit. Its exact statement and proof are
in `3-formalized/positive-quartet-kernels-have-logarithmic-moment-growth.md`.

## Localization — leakage formalized, spectral assembly pending

For a strip trace `F(t)=Σc_j exp(w_j t)`, `|Re w_j|≤D`, put `A=Σ|c_j|`.
A local floor `F(t+x)≥−K` for `|x|≤R` and a positive kernel imply

`∫k(x)F(t+x)dx ≥ −K∫k − A exp(D|t|−qR)∫exp((D+q)|x|)k(x)dx`.

The pointwise proof uses the local floor inside the window and the global
strip envelope outside; no boundary regularity is needed. Countable-support
summation commutes with integration by the absolute moment bound. The
filtered spectrum is exactly the selected quartet.
`PositiveKernelConvolution.integral_kernel_cexp_tsum` formalizes the
interchange for arbitrary index sets by restricting to countable coefficient
support. The tilt moment and transform identities are also proved.

Set `q=T`, `R=8log(T+2)`, `|t|≤T+B`. For `0≤b≤T`, `T≥6`,

`(b+T+6)log(b+T+6)≤6Tlog(T+2)`.

Hence the leakage is `O(exp(DB−T))` once `log(T+2)≥D+1`.
`PositiveKernelLeakage.positive_kernel_logarithmic_floor` proves the exact
error bound `AC exp(DB−T)`. Its local-floor and exponent estimates pass Lean;
all three capstone audits contain only the standard three axioms.
For the shifted trace `exp(-αt)F(t)`, tilt the kernel by `exp(αx)`;
this keeps the original spectral multiplier and replaces `b=D` by
`D+|α|`. Fixed constants affect only the starting height.

Finite-spectrum bounded-gap negative excursions would then force depth
detection on continuous windows `|u−T|≤16log(T+2)`. Prime-gap transfer
supplies prime windows `|log p−T|≤32log(T+2)` after the existing width
iteration `1/2→1/6→0`.

The exact drafted criterion, for `α≥0`, is

`(∀ρ, Re ρ≤1/2+α) ↔ ∃K, arbitrarily late windows of radius 32log(T+2)
have trace ≥−Kp^α at every prime in the window`.

Absolute bounds give the same width. These window conclusions remain
unchecked; they do not produce the arithmetic bound.

## Status

- Existing positive quartet isolation is reused, not claimed as new.
- Theta and positive quartet moment bounds and logarithmic leakage are proved.
  Integral interchange and tilt compensation are proved. The zeta-specific
  spectral assembly and window criteria are under formalization.
- Continuous and prime logarithmic-window criteria remain unproved.
- No arithmetic Stepanov lower bound has been produced. B130 remains open.
- The independently formalized generic positive translation-repair theorem is
  recorded in `3-formalized/positive-laplace-sources-admit-positive-translation-repair.md`.
