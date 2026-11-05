# Truncated quartic flux preserves the fifth even matrix

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Lean:** `ThetaCuspSections/FifthEvenTruncatedQuarticFlux.lean`

For `r≥0`, use the flux
`max(1−r²/2,0)² · thetaCuspCenterCompensationFlux(a,r)`.
Its derivative is continuous, absolutely integrable for `|a|<1`, and has
zero integral over `(0,∞)`. The corrected fifth even source therefore
preserves every actual mixed entry for `0≤a<1/2`.

At and beyond `r=√2`, the correction vanishes. The remaining native source
is strictly positive for every `a>0`: here `π exp(r)≥6`, within the proved
native positivity region.

The double zero makes both the quartic flux and its derivative vanish at
the splice. The polynomial tail identity gives
`∫_(√2,∞) flux' = −flux(√2)=0`; deleting that tail preserves each entry.

Lean namespace `FifthTruncatedCross`: `flux_eq_profile`, `hasDerivAt_flux`,
`continuous_correction`, `integral_deriv_flux`, `weightedRepair_integrable`,
`weightedRepair_integral`, and `weightedRepair_outer_posDef`.
Transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

Remaining Σ6 requirement: positivity throughout the compact interior.
