# Completed-carrier Perron mass discharge

- **ID:** completed-carrier-perron-mass
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** formal Perron carrier interface audit
- **Statement:** The proposed direct use of `completedGN N` in the Perron mass consumers is ill-typed at the analytic level: those consumers require `Differentiable ℂ F`, while `completedGN N` is only proved analytic on the open critical strip.

## Goal
Determine whether concrete mass proofs for `completedGN N` would discharge the carrier hypotheses of
the existing Perron seam theorems.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Failure certificate
`PerronCarrierFlankMass` ultimately consumes a global hypothesis `Differentiable ℂ F`.
`ZetaCarrier.completedGN_analyticAt` and `completedGN_analyticOnNhd_strip` provide analyticity only
for `0 < Re s < 1`.  The direct-plus-reflection identity
`CarrierDepthTwoRigidity.completedGN_eq_direct_add_reflect` assumes `0 < Re s`, so it cannot repair
the negative-integer flanks used by the Perron contour.  Therefore proving only
`HasPerronCarrierFlankL2Energy` and `HasPerronCarrierHorizontalMass` for this object would leave an
unmet global analytic input and would not make the consumer unconditional.

This does not prove that no globally regularized completed carrier can be built.  It proves that the
specific proposed composition through the current `completedGN` definition does not close.

## Log
- 2026-07-10 — Falsified by checking the exact provider and consumer domains; replaced by the live
  globally entire finite-Dirichlet-carrier discharge.
