# HB fixed-propagator global rigidity

- **ID:** HB-FPGR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB `LAND ORIENT DYN`
- **Statement:** For unit seed and any overtone, one divisor-independent universal Peierls propagator realizes every BM boundary target iff RH; no nonzero fixed scalar can realize all targets.

## Goal

Close fixed-propagator global compatibility as an exact RH receiver. This eliminates possibility that a nonzero constant BM incidence survives across all Xi fibres, while leaving literal augmented-source construction as HB producer burden.

## Gates

- [x] 0 → 1 in-progress: source-fixed statement, unconditional Hardy anchor, exact BM zero-locus, proof route identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof below
- [x] 2 → 3 formalized: Lean module and umbrella import; direct check, targeted build, axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition

## Theorem

For every overtone `n`,

`(∃ T, one fixed universal propagator with scalar T realizes every unit-seed BM incidence) ↔ RH`.

Moreover no nonzero `T` realizes every unit-seed BM incidence.

## Proof `[PROVED HERE]`

Existing universal-carrier classification says fixed scalar `T` realizes all incidences exactly when every BM boundary target equals `T`. Hardy's theorem supplies an actual Xi divisor `rho₀` on `Re rho₀ = 1/2`; positive divisor multiplicity supplies a corresponding `XiZeroCopy q₀`. Exact BM target zero-locus gives `Target(q₀)=0`, so global constancy forces `T=0`. Hence every BM target vanishes, and its same exact zero-locus puts every Xi copy on critical line. Existing divisor-exhaustive HB selector theorem then yields RH. Conversely RH places every Xi divisor on critical line, so every unit-seed BM target is zero and the zero propagator realizes all copies. The same Hardy-anchor argument alone excludes every nonzero fixed `T`, without assuming RH.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedPropagatorGlobalRigidity`
- Theorems:
  - `exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh`
  - `not_exists_hbUniversalPeierls_nonzero_fixedPropagator_unit_BM_incidence`
- Axioms: only Mathlib foundations `propext`, `Classical.choice`, `Quot.sound`
- No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration.

## Novelty audit (2026-08-28)

Corpus search found exact arbitrary-incidence realization and fixed-target constancy, but no theorem upgrading fixed global incidence to RH via one unconditional critical anchor. Literature search found standard Peierls/gauge foundations, exact topological-AdS QNM formulas, and Hardy critical-line existence, but no fixed-Peierls-propagator/BM-incidence equivalence or nonzero-constant no-go. Relevant sources: Khavkine, [Covariant phase space, constraints, gauge and the Peierls formula](https://arxiv.org/abs/1402.1282); Aros--Martinez--Troncoso--Zanelli, [Quasinormal modes for massless topological black holes](https://arxiv.org/abs/hep-th/0211024); Sangale, [A note on Hardy's theorem](https://arxiv.org/abs/1606.00680).

## Log

- 2026-08-28 — conjectured from HB corpus target-constancy theorem and unconditional Hardy anchor.
- 2026-08-28 — paper proof closed; Lean proof, targeted build, umbrella wiring, and axiom audit completed.
