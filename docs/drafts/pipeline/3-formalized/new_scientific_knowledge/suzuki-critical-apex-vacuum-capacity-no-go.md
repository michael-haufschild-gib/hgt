# Suzuki critical apex-vacuum capacity no-go

- **ID:** `suzuki-critical-apex-vacuum-capacity-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT RH] [SCALAR TRANSPORT SUBLANE NO-GO]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-critical-apex-vacuum-capacity-no-go.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiCriticalApexVacuumCapacityNoGo.lean`

## Exact theorem surface

- `suzukiCriticalApexVacuumMeasure`: explicit atomless measure obtained by removing density one
  from a width-two rising-flank gap and placing density eight on its final quarter-unit;
- `suzukiCriticalApexVacuumMeasure_Ioc`: its cumulative mass is the explicit monotone piecewise
  law;
- `suzukiCriticalApexVacuumCumulative_band`: `t-2<=F(t)<=t` for every `t`;
- `integral_suzukiCriticalApexVacuumMeasure_eq_quadrature`: exact source-integral identity;
- `suzukiCriticalApexVacuumQuadrature_excess_ge`: actual Suzuki sample-channel excess is at least
  `H_a/128`;
- `integral_suzukiCriticalReflectedArchChannel_le_sixteen`: reflected-polar reserve is at most
  `16`, uniformly in aperture;
- `suzukiCriticalCompletedReserve_le`: full reflected-polar/Gamma reserve is uniformly bounded;
- `exists_atomless_capacityBand_suzukiCompletedLag_violation`: some symbolic aperture has an
  atomless width-two-capacity source that violates completed-lag domination.

## Scientific verdict

This is a class-level falsifier, not another RH criterion.  Any scalar Suzuki proof whose source
information factors only through width-two cumulative capacity, atom-size control or atomlessness,
and an unbounded untouched right-flank apex deficit must also accept the explicit countermodel.
Those data therefore cannot produce the RH-bearing quadrature inequality.

The theorem does **not** prove RH, disprove RH, or rule out source-specific restricted-Weil/Robin
operator identities.  Exact survivor is apex-vacuum amplification: bounded cumulative displacement
can create unbounded error at an exponentially moving apex while leaving opposite flank intact.

## Verification

- direct `lake env lean GaloisForLFunctions/RHTower/SuzukiCriticalApexVacuumCapacityNoGo.lean`:
  pass;
- capstone axioms: only `propext`, `Classical.choice`, `Quot.sound`;
- final cached module build and repository lint: pending final audit.

