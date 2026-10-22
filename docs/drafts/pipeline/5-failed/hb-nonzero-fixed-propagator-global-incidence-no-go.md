# HB nonzero fixed-propagator global incidence no-go

- **ID:** HB-NFPG-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · HB abstract Peierls/global compatibility boundary
- **Statement:** A nonzero divisor-independent scalar on the universal Peierls carrier cannot realize unit-seed BM incidence on every Xi copy.

## No-go closure

- **Exact killing theorem/mechanism:** `not_exists_hbUniversalPeierls_nonzero_fixedPropagator_unit_BM_incidence`. Hardy supplies one genuine critical-line Xi copy; exact BM zero-locus makes its target zero, so any globally constant target is zero.
- **Strongest positive survivor:** `exists_hbUniversalPeierls_fixedPropagator_unit_BM_incidence_iff_rh`. Zero is the sole possible global scalar, and it works exactly under RH.
- **New insight:** Global fixed-propagator compatibility is stronger than copywise abstract realization and carries no adjustable nonzero normalization. Any literal source-fixed Peierls construction proving all-copy incidence closes RH immediately; remaining burden is construction from augmented source, not target selection.
- **Status:** Dependency-closed paper proof and Lean proof in `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedPropagatorGlobalRigidity`; corpus and literature novelty audit recorded on formalized card.

## Log

- 2026-08-28 — nonzero fixed-scalar route retired; exact RH-equivalent zero-scalar survivor formalized.
