# Theta C5 center velocity has a strict likelihood reserve

- **ID:** `C5-VP1-LR`
- **Stage:** 3-formalized
- **Type:** THEOREM / SIGNIFICANT PREMISE DISCHARGE (Lean)
- **Source:** `docs/drafts/pipeline/1-in-progress/theta-cusp-c5-orbit-first-contact.md`
- **Statement:** At every positive radius, the literal modular-center C5 velocity action core is
  strictly larger than an explicit master-reserved core containing no third likelihood jet.  The
  theta support gap pays more than six units of likelihood curvature, so third-cumulant control is
  no longer an open premise of `C5-VP1`.

## Lean artifact

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodReserve`
- Positive-factor normalization:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureVelocity_eq_product_sq_mul_actionCore`
- Exact sign equivalence:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureVelocity_pos_iff_actionCore`
- Exact center likelihood-jet identities:
  `RHTower.thetaCuspReflectedLogJetOne_zero_eq_likelihood`,
  `RHTower.thetaCuspReflectedLogJetTwo_zero_eq_likelihood`, and
  `RHTower.thetaCuspReflectedLogJetThree_zero_eq_likelihood`
- Exact third-channel decomposition:
  `RHTower.thetaCuspReflectedActionFifthRootVelocityCore_zero_eq_lowerJet_sub_thirdLikelihood`
- Strict reserve theorem:
  `RHTower.thetaCuspCenterFifthRootVelocityMasterReservedCore_lt_actionCore`
- Route-facing reduction:
  `RHTower.thetaCuspReflectedSourceFifthRootCurvatureVelocity_zero_pos_of_masterReservedCore_nonneg`

For `t>0`, writing `g₂,g₃` for the second and third likelihood source log-partition jets and
`r = exp(action)-1 > 0`, the exact third channel is `-10*r*t²*g₃`.  Corpus theorem
`6*g₂ < -g₃` yields the strict replacement reserve `60*r*t²*g₂`.  Therefore

`0 ≤ thetaCuspCenterFifthRootVelocityMasterReservedCore(t)`

is now sufficient for strict positivity of the literal center velocity.

## RH-chain consequence

This discharges the complete third-likelihood-cumulant burden in

`C5-VP1`
→ no negative stationary witness
→ modular-center source C5
→ off-center/direct-J rank-four assembly
→ higher-packet no-escape
→ CLG/TTF or Weil positivity
→ RH.

The exact remaining `C5-VP1` premise is unconditional nonnegativity of
`thetaCuspCenterFifthRootVelocityMasterReservedCore` for every `t>0`.  It involves only action,
the first two center jets, and the explicit first-atom third jet.  Proving it closes `C5-VP1`;
downstream assembly obligations remain separate.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ThetaCuspFifthRootCurvatureVelocityLikelihoodReserve.lean`
- targeted
  `lake build GaloisForLFunctions.RHTower.ThetaCuspFifthRootCurvatureVelocityLikelihoodReserve`
- `#print axioms` on normalization, strict reserve, and route-facing reduction
- formal lint gate; new module is reachable from its umbrella

Audited declarations use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.
No conjectural premise, added axiom, `sorry`, `admit`, `opaque`, `unsafe`, or computation occurs.
