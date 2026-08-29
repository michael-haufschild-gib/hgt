# Theta C5 First-Atom-Curvature Seam No-Go

- **ID:** CLG-TTF-C5-VP1-first-atom-curvature-seam-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED / THEOREM (Lean)
- **Date:** 2026-08-29
- **Source:** Exact modular-center fifth-root-curvature velocity, first-atom plus likelihood decomposition, and source seam jets

## Goal

Test and, if false, kill proof-chain entrance

`first-atom-curvature core ≥ 0 for every t > 0`
→ strict modular-center velocity
→ center C5 by seam anchoring and radial monotonicity
→ fixed-action transport and higher-packet assembly
→ CLG/TTF or Weil positivity
→ RH.

## Gates

- [x] 0 → 1 in-progress: corpus-derived `C5-VP1-velocity` chain and hostile falsifier fixed
- [x] 1 → 2 fully-proven: exact seam-jet classification, strict sign, Taylor transfer, and cancellation survivor proved without open dependency
- [x] 2 → 3 formalized: Lean route-kill and survivor theorems; module wired; targeted build and axiom audit pass
- [ ] 3 → 4 publication-ready: standalone exposition and external peer review

## Exact obstruction

Let

- `k = thetaCuspReflectedLogJetTwo 0 0`,
- `B = 2 * thetaCuspBornWittenLogCurvature 1 0`,
- `G = thetaCuspLikelihoodSourceLogPartitionJetTwo 0`.

Smooth right-limit uniqueness closes the missing seam value in the positive-ray atom/likelihood
decomposition and gives `k = B - 2G`. Existing source theorems give `k > 0` and `G > 0`.

The stripped first-atom-curvature core has seam jets

- orders `0,1,2`: zero;
- order `3`: `15*k*(k-B) = -30*k*G < 0`.

Third-order Taylor remainder then makes the actual core negative on a punctured right neighborhood
of zero. Therefore its proposed global nonnegativity premise is formally false.

## No-go closure

- **Exact killing theorem:**
  `not_forall_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_nonneg`.
- **Local mechanism:**
  `eventually_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg`.
- **Strongest positive survivor:** the exact second-likelihood correction has third seam jet
  `30*k*G > 0`, and
  `iteratedDeriv_three_thetaCuspCenterFirstAtomCore_add_secondLikelihoodCorrection_eq_zero`
  proves exact cubic cancellation.
- **Consequence:** likelihood curvature is not a discardable favorable reserve at seam. Any viable
  `C5-VP1-velocity` proof must retain it and control the next surviving jet or full master-reserved
  core. The stripped-core sufficient branch is retired; full center-velocity route remains open.

## Novelty audit

- Internal corpus search found positive-ray curvature decomposition and strict likelihood
  curvature, but no exact seam extension, cubic stripped-core sign classification, local no-go,
  or exact correction cancellation theorem.
- August 2026 literature audit found Planat--Solé,
  [Second-Level Concavity of the Riemann Xi Kernel](https://arxiv.org/abs/2608.19160), proving a
  lower Laguerre/second-level concavity property rather than this fifth-root velocity sign or seam
  cancellation. Corpus no-go theorems already show those lower concavity inputs do not close C5.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspFifthRootCurvatureVelocityFirstAtomCurvatureSeamNoGo.lean`
- Seam decomposition:
  `thetaCuspReflectedLogJetTwo_zero_zero_eq_likelihood`
- Exact stripped-core jets:
  `thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_seamJetClassification`
- Strict cubic sign:
  `iteratedDeriv_three_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg`
- Local negativity:
  `eventually_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_neg`
- Universal-premise route kill:
  `not_forall_thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore_nonneg`
- Exact survivor:
  `iteratedDeriv_three_thetaCuspCenterFirstAtomCore_add_secondLikelihoodCorrection_eq_zero`
- Optimization: universal jet convolution classifiers replace repeated source-specific derivative
  expansion; all checks run at default heartbeat.
- Verification: direct `lake env lean` passed; targeted `lake build` passed; selected endpoint
  theorems use only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-29 — Froze `C5-VP1-velocity` from corpus with exact RH proof chain and physical falsifier.
- 2026-08-29 — First-atom-curvature sufficient core found to have adverse cubic seam jet.
- 2026-08-29 — Proved punctured-neighborhood negativity, killed global premise, and formalized
  exact second-likelihood cubic cancellation as positive survivor.
