# HB passive Darboux optical stationarity no-go

Status: failed/retired
Route: HB
Closed: 2026-08-28

## Proposed route

Use passive absorbed-horizon Darboux scattering or ordinary nonnegative horizon-plus-boundary
transport to force the HC17 equal-positive-weight Peierls Ward identity to vanish.

## Exact obstruction

HC18 constructs the corresponding Peierls optical power and proves

`orbitRadiationPower = 4(8n+5) * transportedOrthogonalHelicityMixingFlux`.

Both factors are nonnegative. For every radiating tilted Xi copy the right side is strictly
positive, not zero. The local Darboux phase mismatch is the same invariant after multiplication by
explicit positive division-free horizon factors. Passive optical transport therefore reinforces
the off-wall Ward defect rather than cancelling it.

## Positive survivor

The premise-free canonical full-Einstein optical reporter has zero power at one Xi copy exactly on
the critical wall, and universal zero power exactly under RH. Its universal stationarity is also
equivalent to the HC17 equal-positive-weight Ward identity.

This survivor is dependency-closed and formalized in
`ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression.lean`. A viable HB action must introduce
a signed cross-sector interference term whose coefficient-exact cancellation is derived from the
action; a sum of passive channel powers cannot work.

## Lean status

- Exact optical bridge: `hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux`
- Strict obstruction: `hbXiPeierlsFESchwarzOrbitRadiationPower_pos_of_tilt`
- Canonical endpoint: `forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh`
- Ward identification: `hbXiPeierlsFESchwarzCanonicalOpticalWard_iff_positiveWard`
- Target build passed; axiom audit contains only Lean/mathlib foundational axioms

## No-go conclusion

Retire passive Darboux/Teukolsky optical transport as a source of stationarity. It provides the
correct positive RH detector but cannot make that detector vanish off wall. Continue only with a
derived signed cross-sector action current, not another nonnegative channel sum.
