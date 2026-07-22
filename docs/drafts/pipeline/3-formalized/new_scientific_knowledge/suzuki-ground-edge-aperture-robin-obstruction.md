# Suzuki ground-edge aperture obstruction and Robin compression — Lean certificate

- **ID:** `suzuki-ground-edge-aperture-robin-obstruction-lean`
- **Stage:** 3-formalized
- **Type:** FORMALIZED THEOREM / RH FRONTIER RELOCATION
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOT AN RH PROOF]`
- **Paper proof:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-ground-edge-aperture-robin-obstruction.md`

## Module

`formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeApertureObstruction.lean`

## Certified declarations

- `exists_smallAperture_suzukiGroundEdgeProfile_gt`: continuity and `g(0)=0` give a uniform
  small-aperture lower profile above any negative threshold.
- `suzukiGroundEdgeAverage_gt_of_lowerMoment`: positive mass transfers a uniform lower moment to
  strict average inequality.
- `suzukiGroundEdgeBoundaryRatio_eq_average_of_flux`: integrated even eigenflux turns source
  average into exact Robin boundary ratio.
- `suzukiGroundEdgeAverage_lt_iff_deficit_gt_excess`: exact deficit/excess classification.
- `suzukiGroundEdgeBoundaryRatio_lt_iff_boundaryMoment_lt`: Robin crossing equals one signed
  boundary-moment inequality.
- `exists_smallAperture_XiC_curvature_half_lt_suzukiGroundEdgeProfile`: specialization to formally
  proved negative Xi curvature.
- `suzukiGroundEdgeAverage_gt_XiC_curvature_of_half_lowerMoment`: exact Xi threshold consumer.

## Scope boundary

Lean certifies topology, order, and boundary-flux algebra without `sorry`, axioms, computations, or
RH premise.  Repository still lacks concrete Suzuki `g`, distributional convolution operator,
ground eigenfunctions, and trace identity.  Those analytic producers are not postulated.

