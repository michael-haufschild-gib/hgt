# Suzuki critical apex-vacuum capacity no-go

- **ID:** `suzuki-critical-apex-vacuum-capacity-no-go`
- **Stage:** 3 — formalized in Lean 4
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT RH] [SCALAR TRANSPORT SUBLANE NO-GO]`
- **Paper proof:**
  `./suzuki-critical-apex-vacuum-capacity-no-go.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalApexVacuumCapacityNoGo.lean`

## Exact theorem surface

- `suzukiCriticalApexVacuumMeasure`: explicit atomless measure obtained by removing density one
  from a width-two rising-flank gap and placing density eight on its final quarter-unit;
- `suzukiCriticalApexVacuumMeasure_Ioc`: its cumulative mass is the explicit monotone piecewise
  law;
- `suzukiCriticalApexVacuumMeasure_Ioc_eq_self_of_outside_gap`: exact capacity-one cumulative mass
  on both exterior flanks;
- `suzukiCriticalApexVacuumCumulative_band`: `t-2<=F(t)<=t` for every `t`;
- `integrable_suzukiCriticalPositiveArchChannel_apexVacuumMeasure`: the actual sample channel is
  integrable against every explicit countermodel;
- `integral_suzukiCriticalApexVacuumMeasure_eq_quadrature`: exact source-integral identity;
- `suzukiCriticalApexVacuumQuadrature_excess_ge`: actual Suzuki sample-channel excess is at least
  `H_a/128`;
- `integral_suzukiCriticalReflectedArchChannel_le_sixteen`: reflected-polar reserve is at most
  `16`, uniformly in aperture;
- `suzukiCriticalCompletedReserve_le`: full reflected-polar/Gamma reserve is uniformly bounded;
- `exists_atomless_capacityBand_suzukiCompletedLag_violation`: some symbolic aperture has an
  atomless width-two-capacity source that violates completed-lag domination.
- `exists_integrable_atomless_capacityBand_flankExact_suzukiCompletedLag_violation_ge`: such a
  source exists beyond every prescribed real aperture threshold, with both exterior flanks exact;
- `not_suzukiCriticalCapacityFlankTailProducer`: no eventual scalar producer can infer completed
  domination solely from integrability, atomlessness, width-two capacity, and exterior-flank
  equality.

## Scientific verdict

This is a class-level falsifier, not another RH criterion.  Any scalar Suzuki proof whose source
information factors only through width-two cumulative capacity, exterior-flank equality,
atom-size control or atomlessness, and an unbounded untouched right-flank apex deficit must also
accept an explicit countermodel beyond every alleged tail threshold.  Those data therefore cannot
produce the RH-bearing quadrature inequality, even eventually.

The theorem does **not** prove RH, disprove RH, or rule out source-specific restricted-Weil/Robin
operator identities.  Exact survivor is apex-vacuum amplification: bounded cumulative displacement
can create unbounded error at an exponentially moving apex while leaving opposite flank intact.

## Verification

- direct `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalApexVacuumCapacityNoGo.lean`:
  pass;
- six new capstone axiom audits: only `propext`, `Classical.choice`, `Quot.sound`;
- targeted leaf build passed:
  `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalApexVacuumCapacityNoGo`;
- repository lint reaches the module but remains red only on three unrelated, concurrently
  untracked BV co-Poisson modules missing from the RHTower umbrella.
