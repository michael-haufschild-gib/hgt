# F2 — uniform resonant-core decay at both endpoints

- **Stage:** 3-formalized
- **Result:** There are `C≥0`, `N∈ℕ` such that every upper Mayer resonance satisfies
  `|core_s(a)|≤C(1+Im s)^N exp(π Im s/2) min(a⁻¹,a^(1−2 Re s))` for all `a>0`.
- **Purpose:** Supply whole-line Haar control and a common Mellin strip for infinite physical synthesis.

## Proof

Set `w=2s`, `r=Re w∈(0,1)`. Theta reciprocity, geometric comparison and the Gaussian integral bound give
`|θRay(t)+1/2|≤min(1/2,√t/π)`.
The exact Mellin identity has value `Γℝ(w)ζ(w)=0`. Its scaled version therefore permits replacing the first factor in the actual theta correlation by `θRay(t)+1/2`.

Using `|θRay(a²t)|≤1/(2a√t)` and splitting at `t=1` gives
`|fieldCore_w(a)|≤[2/(πr)+1/(1−r)]/(|Γℝ(w)|a)`.
The normalized Cauchy density is bounded by `t` below one and `t^(−r−1)` above one. Hence its absolute first moment is at most `(1/2+1/r)/|averagingFactor(w)|`, retaining the outgoing `a⁻¹` bound for the actual period core.

Gamma normalization leaves the coefficient
`[2/(πr)+1/(1−r)](1/2+1/r)|w|π^((r−1)/2)/|Γ((w+1)/2)|`.
The existing zero-free estimate, also applied to the reflected resonance, gives both `1/r≤116 Im s` and `1/(1−r)≤116 Im s`. A fixed-strip Gamma bound absorbs the remaining factors into `C(1+Im s)^N exp(π Im s/2)`. Actual modular inversion turns the outgoing bound into `a^(1−r)` at zero.

## Lean

`RenormalizedIntersectionTheory/MayerScattering/ResonantCoreEndpointBounds.lean`:

- `thetaRay_add_half_norm_le`
- `fieldCore_zero_theta_integral`
- `fieldCore_resonant_endpoint_bound`
- `cauchy_first_mass_le`
- `cauchyCore_resonant_endpoint_bound`
- `upperMayerCore_two_endpoint_growth_bound`

Final individual `lake --old env lean` audit passed without warnings. All three printed endpoints have only `propext`, `Classical.choice`, `Quot.sound`. Module wired into the umbrella.

[Whole-line synthesis and coefficient uniqueness](../1-in-progress/f2-faithful-gaussian-core-completion.md) remain separate obligations. This estimate supplies no Weil sign.
