# Periodic law producer and open-prefix law — Lean certification

- **ID:** ULF-NFD-2
- **Paper card:**
  `periodic-law-producer-phase-quotient-recurrence-and-open-prefix-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.NomogenicFixedPointCalibration`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

`nomogenicHistory_quotient` proves the observer trajectory is the exact quotient of the source
trajectory. `nomogenicSourceHistory_not_period_two` proves one observer period does not close the
source. `nomogenicHistory_no_decoder` proves no function on current observer state reconstructs the
full source trajectory.

`nomogenicSourcePrefix_length` and `nomogenicSourcePrefix_unbounded` certify exact finite-prefix
depth and its unbounded growth. The capstone
`nomogenicPeriodicProducer_phaseQuotient_recurrence_openPrefix` bundles quotient factorization,
period-two observation, nonzero lifted period increment, source nonperiodicity, period-four source
closure, decoder failure, prefix unboundedness, and binary carry.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/NomogenicFixedPointCalibration.lean
lake build GaloisForLFunctions.HTGeometry.NomogenicFixedPointCalibration
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

All checks passed. No `sorry`, new axiom, theorem premise, computation certificate, or unsafe
declaration is used.

## Exact field consequence

One declared producer/quotient package can force recurrent observation, nonclosed lifted state,
nonzero carry, failure of endpoint decoding, and unbounded well-founded approximation depth. The
theorem is a finite calibration only; it does not yet construct the literal HGT producer required
by the NFD field charter.
