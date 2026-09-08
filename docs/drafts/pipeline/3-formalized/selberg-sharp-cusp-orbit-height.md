# Sharp modular orbit height and the excluded core band

- **ID:** SELBERG-SHARP-CUSP-ORBIT-HEIGHT
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 13.
- **Scope:** Actual integral modular matrices acting on the upper half-plane. No spectral conclusion is asserted.

## Exact positive survivor

For every `y>0`, the largest attained imaginary part in the integral modular orbit of `i*y` is

`max(y,1/y)`.

Consequently a cutoff `Y` is reachable from `i*y` if and only if `Y<=max(y,1/y)`.

For every `M>1`, the nonempty open band

`U_M={z : 1/M < Im(z) < M}`

satisfies `Im(g*z)<M` for every `z` in the band and every integral determinant-one matrix `g`. The point `i` lies in every such band.

## Dependency-closed paper proof

The inspected corpus theorem `ThetaCuspHawkingBMCompactModularPeriodization.modular_orbit_height_le` proves

`Im(g*z)<=max(Im(z),1/Im(z))`.

Its proof uses the actual denominator formula: when the lower-left entry is zero, the nonzero integral lower-right entry has square at least one; otherwise the lower-left entry has square at least one and the denominator norm squared is at least `Im(z)^2`.

On the imaginary axis identity attains `y`, while inversion attains `1/y`. This proves the exact attained maximum and the reachability equivalence. If `1/M<Im(z)<M`, both `Im(z)` and its reciprocal are strictly below `M`, proving the band estimate. Continuity of imaginary part makes the band open. Since `M>1`, height one lies strictly inside it.

## Lean implementation and audit

Module: `GaloisForLFunctions.RHTower.SelbergCuspRelocation`.

Capstones: `imaginary_orbit_height_maximum`, `imaginary_reaches_cutoff_iff`, `reciprocal_band_orbit_bound`, `coreBand_no_relocation`, and `exists_open_obstruction`.

The parameterizations `y=exp(h)` and `M=1+exp(u)` cover every allowed positive height and every cutoff above one. All matrices act on the actual upper half-plane; no abstract orbit model replaces the action. Scratch and final direct checks passed without warnings. The targeted final build passed, rebuilding the target and two needed source dependencies. Six axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into its umbrella; no full/umbrella build ran. Final index refresh, formal lint, and whitespace checks passed, with existing large-file lint warnings. No Lean/Lake process remained. Details are recorded in the parent verification log.

## Consequence for the attempted route

Integral cusp relocation alone cannot cover the core by high cusp tails. An estimate involving the core and its boundary must still be proved. This leaves the spectral conjecture and routes coupling core and cusp energies untouched.
