# OWU: blind odd ground source sign

- **ID:** owu-blind-ground-source-sign-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** read-only OWU entry in `docs/reports/rh-current-frontier-map.md`
- **Statement:** [OPEN CORE] Derive a nonnegative blind odd ground minimum from the actual arithmetic source, using and testing the current ground-space polynomial structure without adding a sign premise.

## Goal and plan

OWU only this turn. Earlier thread attempts: XN, HF, IRK, EGC; none credited
with the user's strict significant RH-frontier advance. Full 44-route goal
remains active. Bounds, another receiver/equivalence, and merely easier
formal wrappers do not qualify.

1. Inspect current Lean declarations and corpus search for the exact blind
   constraint, corrected ground space, and canonical generator.
2. Conjecture a source mechanism; attack circularity, loss of blindness, and
   missing positivity. Keep every arithmetic term.
3. Write a dependency-closed paper proof before new Lean code.
4. Formalize only unconditional survivors; one owned Lean build at a time,
   no computations, no axioms/debt, no heartbeat increases, no full builds.
5. Final module and axiom audits, wiring, formal lint, cleanup.

## Initial evidence and question

Frontier entry states corrected odd ground transforms have the form
`P(w²) F_G(w)`, degree below ground-space dimension, with exact finite
spectral interpolation. It also states the canonical ground factor need
not be blind. Inspect the actual domain and image of this polynomial map:
dimension arguments apply only if the entire corrected ground space obeys
the blind constraint. No such claim is assumed.

## Status

- [x] OWU selected; frontier map read-only.
- [ ] Significant obstacle-removing source construction proved.
- [ ] Exact survivor formalized and verified.
- [ ] User's strict contribution criterion met.

## Conjecture log

1. **Polynomial surjectivity forces the canonical generator blind: unsupported.**
   `BlindUnitSource` imposes quadratic autocorrelation constraints at integer
   logarithms. The corrected ground space is linear, but blindness is not.
   `exists_blind_optimizer_common_factor` supplies a blind vector `P(w²)F_G`,
   not blindness of `G`. No dimension argument may silently identify them.
2. **Positive spectral interpolation proves the blind minimum nonnegative:
   circular.** `arithmeticShiftedForm` subtracts `blindMinimum` as well as
   the exact finite arithmetic multipliers. Its proved positivity cannot
   supply the sign of the subtracted number.
3. **Cosine self-duality supplies the blind sign: extra condition remains.**
   `InvertedCosineDistanceGammaPhase` identifies the pole with a positive
   phase-defect integral only for doubly blind cores. Ordinary odd blindness
   does not establish the cosine-dilation constraints. Its resulting total
   multiplier is not pointwise nonnegative either.
4. **Ground simplicity forces a blind canonical factor: open subproblem.**
   A one-dimensional corrected ground space would identify the actual blind
   minimizer with its generator. Existing small-aperture/sign-defect
   simplicity results concern other operators or require sign data; the
   finite Farkas correction here has unrestricted signs. No simplicity claim
   has been proved for this operator.

## Actual unshifted target

`sourceQuadratic_blind_eq_gamma_sub_pole` in
`OddSectorBlindVariationalAttainment.lean` identifies the energy of an odd
blind source exactly as

`∫ 2 gammaHardyPhaseRate(2πξ) |u.freq ξ|² dξ - 2 |<polarVector(1/2),Ju>|²`.

The prime terms vanish; the negative pole term remains. Neither dropping it
nor assuming the Gamma multiplier positive is valid. The needed theorem is
positivity of this full expression on actual blind sources, or another
independent construction removing a stated OWU obstruction.

Corpus searches completed without search errors. Both reported stale
coverage snapshots and unavailable semantic coverage; most candidates have
source-only compiler metadata. Candidate statements were checked in current
Lean source. No new Lean theorem, experiment, web search, or frontier-map
edit has been made in this turn.
