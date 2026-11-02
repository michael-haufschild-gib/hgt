# Zeta zeros and the exact Mellin strip of the scattering core

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** PM
- **Source:** actual scattering core and its certified Mellin transform

Put `F_w(a) = fieldCore w a`, `σ = Re w`, with `0 < σ < 1`, `Im w > 0`.

## Claims

1. If `ζ(w) ≠ 0`, absolute Mellin convergence holds exactly for `0 < Re u < σ`.
2. If `ζ(w) = 0`, absolute Mellin convergence holds exactly for `σ−1 < Re u < 1`.
3. Consequently, convergence at `u=0` characterizes `ζ(w)=0`. At such zeros,
   `M F_w(0) = M F_w(w) = ζ′(w)`.

## Proof mechanism

The certified tail decomposition is
`F_w(a)=T_w(a)−ζ(w)a^(−w)−B(w)a^(−1)`, with
`|T_w(a)| ≤ C(w)a^(−σ/2−1)` for `a≥1`.
Thus `a^w F_w(a) → −ζ(w)`. At a zeta zero, the stronger certified limit is
`a F_w(a) → −B(w)`, with `B(w)≠0`.
A nonzero scaled limit of modulus `L>0` gives, for sufficiently large `a`,
`(L/2)a^(−κ) ≤ |F_w(a)| ≤ (3L/2)a^(−κ)`, with `κ=σ` or `κ=1`.
The weighted norm is therefore comparable to `a^(Re u−κ−1)`.
Its tail integral converges precisely when the exponent is below `−1`; equality
is logarithmic divergence. Local integrability follows by multiplying one
certified central-strip Mellin integrand by its continuous inverse power.
Hence the tail Mellin integral converges exactly when `Re u<σ` in the first
case and `Re u<1` in the second. The exact reciprocity
`F_w(a)=a^(−w)F_w(1/a)` turns the head criterion into the tail criterion
with parameter `w−u`, giving the claimed strips.

For the moment claim, the enlarged strip makes the literal Mellin transform
holomorphic near zero. Its already certified formula on `0<Re u<σ` is
`Γℝ(u)Γℝ(w−u)ζ(u)ζ(w−u)/Γℝ(w)`.
The factors satisfy `u Γℝ(u)ζ(u)→−1` and
`ζ(w−u)/u→−ζ′(w)` at a zero, while `Γℝ(w−u)/Γℝ(w)→1`.
Continuity identifies the limit with the actual moment at zero; reciprocity
gives the moment at `w`.

## Audit and scope

Local corpus contains the core tail, nonzero scattering charge, reciprocity,
and central-strip Mellin formula. Searches found no exact convergence-strip
classification or these derivative moments for this field. This is a local
novelty check, not a literature claim. The endpoint comparison and removable-limit argument are both certified in Lean. No full Mayer eigenspace
classification or Hermitian-form identity is asserted.

## Lean certificates

`RenormalizedIntersectionTheory/GaussMayerZeroMellinStrip.lean` proves
`core_mellinConvergent_iff_of_ne_zero`, `core_mellinConvergent_iff_of_zero`,
and `core_mellinConvergent_zero_iff`, with the incoming limit, exact reflection,
local integrability and endpoint bounds used in their proofs. The production
file passed its direct Lean audit; all ten public declarations use only
`propext`, `Classical.choice`, `Quot.sound`. The derivative moments are certified by
`RenormalizedIntersectionTheory/GaussMayerCoreZeroMoment.lean`: holomorphy
on the enlarged strip and `core_zero_hasMellin_zero`,
`core_zero_hasMellin_parameter`. Its direct production audit passed with the
same three axioms for all three public declarations. Thus both modules have
13 clean public axiom audits. No zero-simplicity assumption is used.
