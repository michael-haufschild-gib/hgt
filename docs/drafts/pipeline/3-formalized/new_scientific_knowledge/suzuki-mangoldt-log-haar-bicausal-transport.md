# Suzuki Mangoldt log-Haar bi-causal transport — Lean formalization

- **Stage:** 3 — formalized in Lean 4
- **Module:** `GaloisForLFunctions.RHTower.SuzukiMangoldtLogHaarTransport`
- **Imported by:** `GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026`
- **Status:** `[FORMALIZED] [AXIOM-CLEAN]`

## Formal declarations

Source and lower law:

- `mangoldtLogHaarMass`
- `mangoldtLogHaarAtomMass`
- `mangoldtLogHaarNode`
- `mangoldtLogHaarMass_succ`
- `monotone_mangoldtLogHaarMass`
- `sum_log_ge_with_endpoint`
- `mangoldtLogHaarNode_sub_two_le_mass`
- `mangoldtLogHaarNode_sub_two_le_mass_pred`

Sharp two-unit interface for known capacity theorem:

- `MangoldtLogHaarCapacity`
- `mangoldtLogHaarSharpPastCell`
- `mangoldtLogHaarSharpFutureCell`
- `mangoldtLogHaarSharpPastCell_length`
- `mangoldtLogHaarSharpFutureCell_length`
- `mangoldtLogHaarSharpPastCell_subset_twoBand`
- `mangoldtLogHaarSharpFutureCell_subset_twoBand`
- `mangoldtLogHaarSharpPastCell_pairwiseDisjoint`
- `mangoldtLogHaarSharpFutureCell_pairwiseDisjoint`
- `mangoldtLogHaarAtom_mul_le_integral_sharpPastCell`
- `mangoldtLogHaarAtom_mul_le_integral_sharpFutureCell`

Fully unconditional formal transport from in-tree Mertens bound:

- `abs_mangoldtLogHaarMass_sub_node_le`
- `mangoldtLogHaarPastCell`
- `mangoldtLogHaarFutureCell`
- `mangoldtLogHaarPastCell_length`
- `mangoldtLogHaarFutureCell_length`
- `mangoldtLogHaarPastCell_subset_nodeBand`
- `mangoldtLogHaarFutureCell_subset_nodeBand`
- `mangoldtLogHaarPastCell_pairwiseDisjoint`
- `mangoldtLogHaarFutureCell_pairwiseDisjoint`
- `mangoldtLogHaarAtom_mul_le_integral_pastCell`
- `mangoldtLogHaarAtom_mul_le_integral_futureCell`
- `mangoldtLogHaar_turningSeam_trichotomy`

Suzuki connector:

- `mangoldtLogHaarAtom_mul_positiveArchSample_eq_two_primeCell`
- `two_vonMangoldt_primeCell_le_integral_sharpPastCell`
- `two_vonMangoldt_primeCell_le_integral_sharpFutureCell`
- `two_vonMangoldt_primeCell_le_integral_pastCell`
- `two_vonMangoldt_primeCell_le_integral_futureCell`

## Boundary

`MangoldtLogHaarCapacity` is a named proposition, not an axiom and not claimed proved in this
module.  It records Ramaré--Zuniga Alterman's known theorem for later full formalization.  Every
theorem without that premise is unconditional and uses only the already formalized Mertens bound.

Remaining RH frontier is not cumulative mass capacity.  It is capacity-preserving splice of
future cells on rising branch with past cells on falling branch inside bounded turning layer.

## Verification

- Direct source check:
  `lake env lean GaloisForLFunctions/RHTower/SuzukiMangoldtLogHaarTransport.lean` — passed.
- Final umbrella audit:
  `lake build GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026` — passed `9513/9513`.
- Nine capstone axiom surfaces contain only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan is clean.
- Repository lint reaches this module; its remaining 22 failures are unrelated shared-tree
  unreachable modules.
