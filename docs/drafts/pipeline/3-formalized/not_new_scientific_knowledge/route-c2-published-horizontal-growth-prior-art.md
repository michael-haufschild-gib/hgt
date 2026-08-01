# Route C2 published horizontal-growth prior art

- **ID:** `route-c2-published-horizontal-growth-prior-art`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXPLICIT PRIOR-ART OWNERSHIP
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Sondow--Dumitrescu own strict horizontal Xi-modulus monotonicity in zero-free
  half-planes; Planat's June 2026 paper owns theta-kernel positivity framing and localization of the
  remaining obstruction to the critical aperture.

## Ownership boundary

Primary sources:

1. J. Sondow and D. Dumitrescu, *A monotonicity property of Riemann's xi function and a
   reformulation of the Riemann Hypothesis*, arXiv:1005.1104,
   <https://arxiv.org/abs/1005.1104>.
2. M. Planat, *A Theta-Kernel Reformulation of a Growth Theorem and the Riemann Hypothesis*, posted
   2026-06-01, <https://www.preprints.org/manuscript/202606.0062>.

These results are formalized so downstream cards cannot relabel them as project novelty. The
separate zero-safe odd divisor germ remains classified conservatively as an internal bridge with
external novelty unverified.

## Lean theorem surface

Module: `RHTower/ThetaCuspCenterMixedPublishedGrowthPriorArt.lean`.

- `xiRelativeResolventTerm_lineConj_pair_im_pos_of_halfPlaneBound`: strict paired atom sign.
- `xiRelativeResolventTrace_im_pos_of_halfPlaneBound`: strict full trace sign.
- `thetaXiHankelOrbit_kreinForm_pos_of_halfPlaneBound`: strict source-current sign beyond the zero
  width.
- `strictMonoOn_normSq_XiC_horizontal_of_halfPlaneBound`: strict squared-modulus growth.
- `strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound`: exact strict modulus growth on
  `[alpha,infinity)`.
- `PlanatThetaKernelCriticalApertureNonnegative`: exact critical-aperture coupled-kernel predicate.
- `planatThetaKernelCriticalApertureNonnegative_iff_riemannHypothesis`: critical theta-kernel
  positivity endpoint.
- `thetaCuspCenterMixed_publishedGrowthLocalization_package`: exact coupled-cone representation,
  unconditional exterior positivity, and remaining critical-aperture localization.

## Anti-theatre audit

- Strictness is proved by one strictly positive paired atom plus summability; no `≥ 0` surrogate.
- Modulus monotonicity is stated for the literal centered Xi function, not an abstract proxy.
- Theta-kernel theorem uses the literal source current and exact coupled-cone integral.
- No theorem in this card is presented as new knowledge or as an RH proof.

## Verification

- [x] unconditional source check with `lake env lean`
- [x] umbrella import wired
- [x] axiom audit; repository lint reaches this module and reports only two unrelated untracked
  modules missing umbrella imports
- [x] full build intentionally omitted per user instruction

## Log

- 2026-08-01 — exact published strict-growth and theta-kernel localization surfaces formalized and
  separated from the new zero-safe divisor bridge.
