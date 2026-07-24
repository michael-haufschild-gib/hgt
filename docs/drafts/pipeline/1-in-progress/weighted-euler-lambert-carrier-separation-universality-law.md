# Weighted-Euler Lambert carrier-separation universality law

- **ID:** weighted-euler-lambert-carrier-separation-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of compact-carrier exponential decay, quantitative
  Möbius ray recovery, and two-functional Fourier--Borel carrier separation
- **Statement:** For two continuous functionals on one compact carrier whose coordinate real
  parts lie in a positive strip `[α, β]`, uniform geometric decay of the Lambert transform of
  their difference along every positive multiplicative ray, at a base-point rate `σ > β`,
  forces their Fourier--Borel transforms to agree identically.

## Goal

Close the quantitative pipeline explicitly advertised but not completed by the existing
Weighted-Euler modules. The lower carrier wall must generate the geometric input required by
Möbius recovery; the recovered base-ray estimate must then cross the upper carrier wall and
trigger global separation.

## Gates

- [x] 0 → 1 in-progress: full read of carrier-separation, FE-separation, compact Lambert, and
  quantitative Möbius-recovery endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check
- [x] 3 → 4 novelty audit: post-proof literature search found no collision

## Corpus inputs

- `norm_compactExponentialTest_le_exp_neg_of_re`
- `norm_compactFourierBorel_le_of_sampled_lambert_decay`
- `compactFourierBorel_sub_eq_zero_of_ray_decay`
- linearity of a continuous linear functional on the compact exponential and Lambert tests

## Proof

**[PROVED HERE]** Put `L = L₁ - L₂`. Fix a positive real base point `x`. Since
`Re(s(k)) ≥ α > 0`, at every positive integer multiple `n x` the compact exponential test has
norm at most

`exp(-n α x) = exp(-α x)^n`,

and `exp(-α x) < 1`. Applying `L` therefore supplies the geometric Fourier--Borel ray bound
required by quantitative Möbius recovery. The assumed Lambert estimate supplies its second
input with amplitude `D exp(-σ x)` and geometric ratio `ρ ≤ 1/2`. Recovery gives

`‖FB_L(x)‖ ≤ 4 D ρ exp(-σ x)`.

Linearity identifies `FB_L = FB_{L₁} - FB_{L₂}` and likewise identifies the assumed Lambert
transform with the difference channel. At `x = 0`, the ordinary operator-norm estimate bounds
the difference by `‖L‖`. Thus one global constant

`C = max (4 D ρ) ‖L‖`

bounds the Fourier--Borel difference by `C exp(-σ x)` for every `x ≥ 0`. Finally
`Re(s(k)) ≤ β < σ`; two-functional carrier separation forces the two Fourier--Borel transforms
to agree at every complex point. ∎

## Strict gain over corpus endpoints

The corpus separately contains raywise Möbius recovery and carrier separation. No endpoint
turns one uniform Lambert sampling estimate into global equality of two compactly carried
functionals. The new law removes the intermediate Fourier--Borel decay hypothesis and derives
it from the lower carrier wall.

## Lean formalization

- Main theorem:
  `compactFourierBorel_eq_of_uniform_sampled_lambert_decay`
- Module:
  `GaloisForLFunctions.RHTower.WeightedEulerLambertCarrierSeparationUniversalityLaw`
- Verification:
  `lake env lean GaloisForLFunctions/RHTower/WeightedEulerLambertCarrierSeparationUniversalityLaw.lean`
  passed without warnings.
- Umbrella:
  imported by `GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Post-proof searches found classical Lambert-series Möbius inversion, Paley--Wiener carrier and
exponential-type uniqueness theorems, and arithmetic asymptotics for Möbius-twisted Lambert
series. No source states the positive-strip compact-functional theorem that turns uniform
multiplicative-ray Lambert decay into equality of two entire Fourier--Borel transforms. Novelty
remains a negative-search conclusion, not a claim of bibliographic completeness.

## Log

- 2026-07-23 — terminal component read; corpus search found no Lambert-to-separation theorem.
- 2026-07-23 — positive-strip Möbius-recovery/separation proof completed before Lean source or
  literature search.
- 2026-07-23 — exact-file Lean verification passed; module wired into the RHTower umbrella.
- 2026-07-23 — post-proof literature audit found no exact or equivalent law.
