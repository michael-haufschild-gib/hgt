# Prime-archimedean cofinal orientation-charge universality

- **ID:** prime-arch-cofinal-orientation-charge-universality
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `PrimeArchCofinalSourceTemperatureMaster` and `PrimeArchExactOffLineQuartetKMSMaster`
- **Statement:** For every pair of cofinal finite-volume and cooling schedules, vanishing of the exact quartet thermal orientation energy is equivalent to cofinal Bernstein negative-mass vanishing, source response above four, zero free-energy rate, subexponential growth, and recurrent boundedness.

## Goal

Identify one schedule-independent intrinsic scalar governing every cofinal two-scale thermal phase.

## Gates

- [x] 0 → 1  in-progress: exact common RH interface identified from Lean theorem statements
- [x] 1 → 2  fully-proven: dependency-closed equivalence proof
- [x] 2 → 3  formalized: exact Lean theorem, direct elaboration, final module build, lint, and axiom audit pass
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

`CofinalHausdorffBernsteinNegativeMassVanishing`, every cofinal schedule condition, and the
positive-frequency response above four are each equivalent to RH in the source-temperature
theorems.  The exact quartet theorem proves `xiThermalOrientationEnergy = 0 ↔ RH`.  Transitivity
gives every displayed equivalence, uniformly in both schedules.

## Audit

- **[CORPUS]:** `cofinalPrimeArchHausdorffBernsteinNegativeMassVanishing_iff_riemannHypothesis`
- **[CORPUS]:** `continuedPrimeArchPositiveFrequencyAbove_four_iff_cofinalBernsteinNegativeMass`
- **[CORPUS]:** three cofinal thermal-section RH equivalences
- **[CORPUS]:** `xiThermalOrientationEnergy_eq_zero_iff_rh`
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; not present as a direct scalar-to-all-schedules theorem
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`; development Lean file passes direct elaboration, final formal gates pending

## Log

- 2026-07-22 — whole-corpus closure found; paper proof closed; exact Lean development theorem written
