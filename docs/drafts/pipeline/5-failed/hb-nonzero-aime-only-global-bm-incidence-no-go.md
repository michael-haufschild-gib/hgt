# HB nonzero AIME-only global BM incidence no-go

- **ID:** HB-NAOGBI-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · HB `DYN ORIENT LAND`
- **Statement:** No fixed nonzero normalization of a nonzero fundamental AIME cross-branch residue can realize the unit-seed BM Peierls target on every Xi fibre.

## No-go closure

- **Exact killing theorem/mechanism:** `not_exists_nonzero_normalizedAIMEResidue_global_unitBMTarget`. Hardy supplies a critical Xi copy where BM target vanishes, while source-derived AIME residue is nonzero exactly for nonzero absorbed seed.
- **Strongest positive survivor:** `d4FullCrossBranchProjectedResidue_eq_unitBMTarget_iff_samePoleSource`. Full incidence uniquely requires `Remainder = JostDerivative · BMTarget - AIMENumerator`; on a critical copy this becomes the nonzero forced counterterm `-AIMENumerator`.
- **New insight:** Absorption-induced mode excitation is genuine nonlinear gravitational support but has wrong global zero geometry for BM incidence. Literal HB producer must contain an additional same-pole third-order `++-` source; multiplicative normalization, horizon phase, and AIME alone cannot supply it.
- **Status:** Dependency-closed paper proof and Lean proof in `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingAIMEBMGlobalSourceIncompatibility`; targeted build and axiom audit pass. Formalized survivor card records novelty audit.

## Log

- 2026-08-28 — AIME-only route retired; exact nonzero third-order same-pole repair law preserved.
