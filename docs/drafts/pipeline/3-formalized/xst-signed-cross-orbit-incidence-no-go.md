# XST signed cross-orbit incidence no-go

- **ID:** xst-signed-cross-orbit-incidence-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · XST open core
- **Statement:** No transposition-odd, coefficient-faithful incidence on the full primitive-direction current family exists, even without linearity, continuity, boundedness, or support restrictions.

## Goal

Kill `transpose-fixed primitive currents → signed cross-orbit incidence → ambient spin inheritance → RH`.

## Gates

- [x] Corpus-derived RH chain and exact open-core interface
- [x] Dependency-closed proof
- [x] Lean theorem and source check
- [x] Targeted build and axioms audit
- [ ] Publication-ready

## Proof

The complete current family is fixed by simultaneous primitive-coordinate transposition. Any signed equivariant reporter therefore equals its negative and vanishes. Its claimed Xi-divisor landing reduces to vanishing of the centered Hurwitz monodromy defect, hence to ambient-spin inheritance and globally RH. Pre-divisor coefficient faithfulness is impossible already at exponent `1/2`, whose monodromy cannot equal `1`.

## No-go closure

- **Exact killing theorem:** `xst_signedCrossOrbitIncidence_noGo`.
- **Strongest positive survivor:** `XSTSignedCrossOrbitIncidence.current_eq_zero` classifies the whole nonlinear, infinite, cross-orbit interface; `everyXSTSignedCrossOrbitSpinLanding_iff_riemannHypothesis` proves every remaining landing is circular.
- **New insight:** distinct transpose orbits do not help while the full source and reporter remain equivariant. Any successor needs independently derived source data that breaks primitive-coordinate transposition symmetry; this is outside XST's stated architecture.
- **Status:** `RHTower/XiCTaylorPrimitiveDirectionSignedCrossOrbitNoGo.lean`; targeted build passes in 110s; standard axioms only. Literature search through 2026-09 found the general equivariant fixed-point principle but no theta/Xi/RH cross-orbit application; exact result is corpus-new.
