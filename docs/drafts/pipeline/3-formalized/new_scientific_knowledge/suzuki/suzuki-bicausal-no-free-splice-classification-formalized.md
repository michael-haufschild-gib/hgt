# Suzuki bicausal no-free-splice classification

- **ID:** `suzuki-bicausal-no-free-splice-classification`
- **Stage:** 3 — formalized in Lean 4
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [NO RH PREMISE] [NOT RH]`
- **Paper proof:**
  `./suzuki-bicausal-no-free-splice-classification.md`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiBicausalNoFreeSplice.lean`

## Formal surface

- `GaloisForLFunctions.HTGeometry.bicausalLeftTarget_union_rightTarget`:
  future and past targets cover the capacity-one interval;
- `GaloisForLFunctions.HTGeometry.bicausalLeftTarget_inter_rightTarget`:
  their intersection is exactly the displacement seam;
- `suzukiBicausalMixedTargetMass_eq_capacity_add_seam`:
  mixed integral equals capacity-one integral plus seam integral;
- `suzukiBicausalCapacityCorrectedResidual_eq_deficit`:
  seam-corrected mixed residual is identically original quadrature deficit;
- `suzukiBicausalSlack_pays_seam_iff_capacity_dominates`:
  seam payment is equivalent to original capacity-one domination;
- `suzukiBicausalContinuumSlack_eq_seam`:
  continuum splice has zero corrected margin.

## Scientific boundary

Formal theorem retires inference that critical tilted-tent total apex deficit pays duplicate seam.
It does not prove or assume Mangoldt quadrature domination.  Surviving RH problem is independent
source control of arithmetic displacement residual after restricted-Weil/Robin/Gamma assembly.

## Audit

- targeted `lake env lean` check: pass;
- target-only cached `lake build GaloisForLFunctions.RHTower.SuzukiBicausalNoFreeSplice`: pass;
  Lake replayed cached dependencies and built only
  `GaloisForLFunctions.HTGeometry.BicausalDisplacementOverlap` and
  `GaloisForLFunctions.RHTower.SuzukiBicausalNoFreeSplice`;
- axiom audit: pass; all six audited declarations depend only on `propext`,
  `Classical.choice`, and `Quot.sound`;
- umbrella imports:
  `GaloisForLFunctions.RHTower` and
  `GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026`.
