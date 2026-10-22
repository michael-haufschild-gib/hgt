# HB nonzero fixed-skew-propagator global incidence no-go

- **ID:** HB-NFSPG-NG
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · HB abstract Peierls/global compatibility boundary
- **Statement:** A nonzero divisor-independent complex-linear skew propagator on the universal carrier cannot realize unit-seed BM incidence on every Xi copy.

## No-go closure

- **Exact killing theorem/mechanism:** `not_exists_hbUniversalPeierls_nonzero_fixedSkewPropagator_unit_BM_incidence`. Universal-carrier skew classification reduces every candidate to one scalar symplectic rotation; Hardy's critical copy forces that scalar to zero.
- **Strongest positive survivor:** `exists_hbUniversalPeierls_fixedSkewPropagator_unit_BM_incidence_iff_rh`. An arbitrary fixed skew propagator exists exactly under RH, and classification makes the zero propagator its sole possible value.
- **New insight:** Enlarging the scalar ansatz to every complex-linear skew endomorphism adds no freedom at all in the two-dimensional universal Peierls carrier. Remaining HB producer burden cannot be evaded by choosing a more general abstract skew map; it must derive global incidence from literal augmented Einstein--Teukolsky source dynamics.
- **Status:** Dependency-closed paper proof and Lean proof in `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMUniversalSkewPropagatorClassification` and `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMUniversalSkewPropagatorGlobalRigidity`; novelty audit recorded on formalized card.

## Log

- 2026-08-28 — nonzero arbitrary-skew route retired; exact RH-equivalent zero-propagator survivor formalized.
