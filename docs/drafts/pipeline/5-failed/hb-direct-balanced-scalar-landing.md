# HB direct balanced scalar landing

- **ID:** HB-C-A.9v-direct
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/hb-complete-augmented-third-order-source-coefficient.md · C-A.9v
- **Statement:** C-A.9u plus zero first/second cusp finite parts directly identifies the actual
  balanced `++-` coefficient with the corpus canonical four-Xi vertex.

## Goal

Test earliest claimed post-C-A.9u landing before spending work on negative BM and left-QNM
propagation.

## Gates

- [x] 0 → 1 in-progress: exact source chain and hostile kill criterion frozen
- [x] 1 → 2 fully-proven: dependency-closed residual and normalization proof
- [x] 2 → 3 formalized: Lean no-go and positive survivor; targeted build green
- [ ] 3 → 4 publication-ready: not a standalone publication target

## Approach

Apply an arbitrary complex-linear height finite-part reporter to the literal C-A.9u identity,
subtract the canonical Stokes-completed identity, and retain every residual.  Independently compare
the classical completed-Lambda RSZ numerator with the corpus pole-filled four-Xi vertex at a regular
absolute-convergence point.

## No-go closure

- **Exact killing theorem/mechanism:** Lean proves
  `balancedResidual = B * scalarResidual + cuspResidual`.  Thus zero cusp data leaves the scalar
  RSZ residual untouched.  An extraction datum at `s=t=2`, where `B=-4`, satisfies the exact
  boundary-free extraction law but misses canonical landing.  More strongly, the classical
  completed-Lambda RSZ value is nonzero there and the canonical pole-filled value is exactly ten
  times it, so direct normalization equality is false away from all poles.
- **Strongest positive survivor:** For every abstract complex-linear height reporter with zero
  first/second cusp values and nonzero `B`, canonical balanced landing is equivalent to canonical
  pole-filled scalar RSZ landing.  C-A.9w subsequently proves that such a height reporter cannot
  represent analytic-family regularization uniformly after spectral specialization; the genuine
  survivor must remain a meromorphic parameter-family identity before specialization.
- **New insight:** Scalar RSZ is not optional infrastructure after C-A.9u.  It is the necessary and
  sufficient next analytic theorem.  Correct surviving chain is
  `pole-filled scalar RSZ -> C-A.9u -> actual balanced ++- landing -> negative BM -> left-QNM ->
  HC94 cocycle -> RH`.
- **Status:** Paper proof dependency-closed.  Lean module
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinScalarLandingNoGo`; headline theorems
  `d4BM_actualBalancedCanonicalLandingResidual_eq`,
  `d4BM_actualBoundaryFreeCanonicalBalancedLanding_iff_scalarRSZ`,
  `d4BM_directScalarLanding_from_zeroCusp_not_forced`, and
  `d4BM_canonicalScalarVertex_ne_classicalCompletedRSZ_at_two`.  Direct Lean and targeted build
  `12476/12476` pass.  Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Primary-source audit through 2026-08-29: Zagier's scalar regularized triple-Eisenstein formula is
classical (p. 431, <https://people.mpim-bonn.mpg.de/zagier/files/rankin-selberg/fulltext.pdf>), with
modern regularization extensions in Wu (<https://arxiv.org/abs/1810.09437>).  Neither audited
literature nor corpus contains this source-normalized HB residual classification or balanced-source
necessity theorem.  Novelty claim is restricted accordingly.

## Log

- 2026-08-29 — direct landing falsified; positive survivor formalized and audited
- 2026-08-29 — C-A.9w correction: reporter algebra remains valid, but pointwise interpretation as
  analytic-family finite part is independently retired
