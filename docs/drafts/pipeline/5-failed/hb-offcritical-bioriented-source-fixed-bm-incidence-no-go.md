# HB off-critical bioriented source-fixed BM incidence no-go

- **ID:** HB-OBSBI-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · HB `LAND ORIENT DYN`
- **Statement:** A single cyclic/skew Peierls structure whose physical branches swap under Schwarz reflection cannot realize the literal Hermitian BM candidate in both orientations at an off-critical Xi fibre.

## No-go closure

- **Exact killing theorem/mechanism:** `d4BMXiSourceFixedPeierls_BM_incidence_forces_criticalLine`. Schwarz branch swap and Peierls skewness make the cubic cut reflection-odd, while the reflected literal BM candidates sum to twice a Hermitian current whose zero locus is exactly the critical line.
- **Strongest positive survivor:** `d4BMXiSourceFixedPeierls_global_BM_incidence_forces_rh`. One source-fixed Schwarz-covariant Peierls incidence valid on every Xi copy proves RH; bioriented/global compatibility is automatic rather than an extra dynamical premise.
- **New insight:** Off-critical failure cannot be repaired by selecting a second orientation law independently. Any successful literal HB construction must either violate the physical Schwarz branch swap, violate cyclic/skew Peierls structure, or fail BM source incidence. For the intended variational theory only incidence remains open.
- **Status:** Dependency-closed paper proof and Lean proof in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFixedPeierlsReflectionRigidity`; targeted build and axiom audit pass. Formalized survivor card records literature audit.

## Log

- 2026-08-28 — off-critical bioriented source-fixed BM incidence retired; automatic compatibility and global RH reduction preserved.
