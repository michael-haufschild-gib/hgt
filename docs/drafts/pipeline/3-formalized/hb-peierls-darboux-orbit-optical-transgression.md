# HB Peierls--Darboux orbit optical transgression

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC18

The HC16 FE--Schwarz Peierls orbit trace and the corpus Darboux absorbed-horizon phase mismatch
are two exact normalizations of the same nonnegative orthogonal-helicity mixing invariant. For
`a=Re(q)`, `b=Im(q)`, reflected Darboux weights `c,d`, drive
`y=12 horizonAmplitude^2 omega`, and `N=8n+5`, prove

`b^2(c^2+y^2)(d^2+y^2) mismatch * N`

`= -16 y^2 a^2(1-a)^2 * Re(orbitTrace)`.

Transport this identity through arbitrary radiation maps, classify its zero locus, and construct a
premise-free full-Einstein reporter whose universal stationarity is equivalent to RH.

## Result

HC18 holds with exact coefficient `-16`. The local division-free phase-mismatch identity is proved
for every Xi copy, Peierls order, amplitude, and frequency, without nonvanishing assumptions.

For any complex-linear radiation map, define

`orbitRadiationPower = -Re(orbitTrace) * ‖radiation psi‖^2`.

Lean proves the exact transported law

`orbitRadiationPower = 4(8n+5) * transportedOrthogonalHelicityMixingFlux`.

Hence this power is nonnegative, is strictly positive for every radiating tilted Xi copy, and
vanishes exactly on the critical wall. The Darboux phase-mismatch radiation energy satisfies the
same coefficient-exact transgression after its division-free horizon factors are restored.

Specializing to the gauge-fixed full-Einstein second-harmonic radiation map, unit absorbed
amplitude, and zero auxiliary mixing produces a canonical reporter with no premises. Its universal
vanishing is equivalent to RH and exactly equivalent to HC17 equal-positive-weight Ward
stationarity.

## Main Lean theorems

- `hbXiPeierlsFESchwarzOrbitDarbouxPhaseMismatch_optical_eq`
- `hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux`
- `hbXiPeierlsFESchwarzOrbitRadiationPower_nonneg`
- `hbXiPeierlsFESchwarzOrbitRadiationPower_eq_zero_iff_line`
- `hbXiPeierlsFESchwarzOrbitRadiationPower_pos_of_tilt`
- `hbXiPeierlsFESchwarzOrbitDarbouxRadiation_optical_eq`
- `hbXiPeierlsFESchwarzFullEinsteinOrbitRadiationPower_eq_zero_iff_line`
- `forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh`
- `hbXiPeierlsFESchwarzCanonicalOpticalWard_iff_positiveWard`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression.lean`

## New knowledge

The global Peierls trace, local Darboux horizon phase mismatch, and transported full-Einstein
orthogonal-helicity flux are not merely zero-locus-equivalent: they obey one exact normalization
law. The factor `4(8n+5)` converts Peierls orbit trace power into transported optical flux, while
the factor `-16 y^2 a^2(1-a)^2` gives its division-free horizon phase form.

This replaces HC17's abstract positive Ward endpoint by a literal optical observable. It also
proves a sharp physical obstruction: passive horizon-plus-boundary transport makes the missing
Ward defect strictly positive off wall, so passivity cannot supply stationarity. A successful HB
proof must add a genuinely signed cross-sector action cancellation; proving canonical optical
darkness itself is already RH.

## Literature audit through 2026-08-28

Primary literature contains black-hole Darboux transformations and isospectrality, rigorous
Teukolsky scattering, Kerr reflection currents, absorption-induced nonlinear mode excitation, and
covariant Peierls brackets. Search found no Xi-divisor FE--Schwarz Peierls orbit trace, no exact
Peierls-to-Darboux/helicity-flux normalization, and no canonical optical-darkness RH equivalence:

- Glampedakis--Johnson--Kennefick, *The Darboux transformation in black hole perturbation theory*,
  https://arxiv.org/abs/1702.06459
- Masaood, *A Scattering Theory for Linearised Gravity on the Exterior of the Schwarzschild Black
  Hole I: The Teukolsky Equations*, https://arxiv.org/abs/2007.13658
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Sberna et al., *Nonlinear effects in the black hole ringdown: absorption-induced mode
  excitation*, https://arxiv.org/abs/2112.11168
- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282

Novelty claim is the exact transgression, strict-passivity no-go, premise-free canonical reporter,
and RH/Ward equivalences, not the separate classical frameworks.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression`
- Build result: success, 11905 jobs after shared dependency replay
- `#print axioms` on seven endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token and diff-whitespace scans: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; this module is reachable and
  has no lint finding

## Remaining HB burden

Derive a signed cross-sector action/current identity that cancels the strictly positive canonical
optical power. HC18 proves no passive one-channel optical theorem can do this. Any premise-free
derivation of canonical optical stationarity closes HB by proving RH.
