# Suzuki transition-core completed Xi residue fission

- **ID:** SP-E-XI-FISSION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** rh-current-frontier-map.md · SP-E/Route-P
- **Statement:** Every retained ordered transition pair descends through the completed quadratic source current to every Xi multiplicity copy, and total corner energy is exactly one half of multiplicity times transition core times base-conormal norm square.

## Goal
Close source occurrence, ordered pair coefficient fidelity, both residue orientations, and analytic multiplicity on one Xi carrier without RH.

## Gates
- [x] 0 → 1  source-pure pre-divisor gauges and exact pair labels
- [x] 1 → 2  dependency-closed proof
- [x] 2 → 3  `SuzukiTransitionCoreCompletedXiResidueFission.lean`; targeted leaf build and axiom audit pass
- [ ] 3 → 4  publication-ready

## Approach
Insert square-root Cartan cell amplitude before either completed-source pole limit, split analytic multiplicity before residues, take reflected and forward limits separately, and sum exact copy energies.

## Log
- 2026-08-31 — Formalized. `two_mul_suzukiTransitionCoreXiFibreCornerEnergy_eq`; only `propext`, `Classical.choice`, `Quot.sound`.
