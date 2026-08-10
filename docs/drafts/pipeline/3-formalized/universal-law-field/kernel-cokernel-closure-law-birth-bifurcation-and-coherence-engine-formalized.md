# Kernel--cokernel--closure law-birth bifurcation and coherence engine — formalized

- **ID:** ULF-KCL-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper source:** kernel-cokernel-closure-law-birth-bifurcation-and-coherence-engine.md
- **Lean module:** GaloisForLFunctions.HTGeometry.ConstitutiveCarrierBifurcation
- **Status:** [FORMALIZED] [NO PROJECT AXIOMS] [UMBRELLA-BUILT]

## Certified mechanism

Lean proves:

1. **higherBirthObstruction_eq_zero_iff_exists** — algebraic carrier class vanishes exactly when
   associator has a carrier preimage;
2. **separatedHigherBirthObstruction_eq_zero_iff_approximable** — separated class vanishes exactly
   when associator lies in closure of carrier range;
3. **higherBirthCarrier_phase_trichotomy** — exact, mirage, or separated phase;
4. **higherBirthObstruction_maps_to_separated** — canonical Hausdorff transition;
5. **higherBirthObstruction_pentagon** and
   **separatedHigherBirthObstruction_pentagon** — both quotient laws retain coherence;
6. **higherCarrierLift_residual_mem_kernel** — next coherence defect of every carrier lift lands
   in carrier kernel;
7. **higherCarrierLift_pentagon_of_injective** — injective carriers reflect coherence;
8. **no_mirage_of_closed_range** — closed range excludes approximable-only birth;
9. **exists_dense_mirage_higher_birth** — unconditional compact injective
   dense/non-surjective Hilbert countermodel;
10. **kernelAmbiguousHigherCarrier_residual_nonzero** — unconditional
    surjective/noninjective kernel-ambiguity countermodel;
11. **carrierBifurcationMechanism_closed** — one closed theorem bundles both independent failures.

## Verification

- direct foreground command:
  lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCarrierBifurcation.lean;
- formal lint: python3 scripts/formal_tools.py lint;
- axiom audit: only propext, Classical.choice, Quot.sound;
- umbrella import: GaloisForLFunctions.HTGeometry.UniversalLawField;
- final audit: lake build GaloisForLFunctions.HTGeometry.UniversalLawField;
- result: 11,537 jobs, success.

Build emitted only pre-existing replay warnings in unrelated modules. New module built cleanly.

## Scope

Formalization certifies one-stage linear/additive mechanics. It does not certify naturality under
carrier squares, composition of successive carrier refinements, nonlinear torsors, source genesis,
or any RH application.

## Log

- 2026-08-10 — direct elaboration, lint, axiom audit, umbrella wiring, and final build passed.
