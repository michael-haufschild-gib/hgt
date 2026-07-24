# Perron Strip-Mass / Dirichlet Depth-Two/Three Blindness Universality Law

- **ID:** LAW446
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean target)
- **Source:** Lean-corpus synthesis of
  `PerronStripMassDischarge.lean` and
  `DirichletDepthTwoThreeZeroTransitionUniversalityLaw.lean`
- **Statement:** At every admissible Perron contour, depth-two and depth-three Dirichlet carriers
  satisfy the same explicit strip-mass envelope, yet depth two is zero-free in the right
  half-plane while depth three has open-strip zeros at arbitrarily large heights.  Hence strip
  mass alone cannot force eventual open-strip zero-freeness.

## Goal

Extract the sharp positive survivor from comparing the discharged Perron contour theory with the
finite Dirichlet zero transition: an exact limitation theorem for what aggregate boundary mass can
detect.

## Gates

- [x] 0 → 1 in-progress: common finite-Dirichlet carrier and incompatible zero phases found
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized:
  `perronStripMass_depthTwoThree_blindnessUniversality`;
  `lake env lean GaloisForLFunctions/RHTower/PerronStripMassDepthTwoThreeBlindnessUniversalityLaw.lean`
  clean; imported by `GaloisForLFunctions/RHTower.lean`
- [ ] 3 → 4 publication-ready: pending standalone exposition and external novelty review

## Statement

For every admissible `c,n,δ,M`, let `L₂` and `L₃` be the explicit Perron strip-mass bounds for
`dirichletPoly 2` and `dirichletPoly 3`, and set `L = max L₂ L₃`.  Then:

- both carriers satisfy `HasPerronStripMassAt ... L`;
- `dirichletPoly 2` is zero-free whenever `Re s > 0`;
- for every height `B`, `dirichletPoly 3` has a zero `s` with
  `0 < Re s < 1` and `B ≤ Im s`;
- the universal rule saying that `HasPerronStripMassAt ... L` forces eventual open-strip
  zero-freeness is false.

## Paper proof

The Perron strip-mass discharge theorem supplies explicit bounds `L₂` and `L₃`.  The four
components of `HasPerronStripMassAt` are monotone in the final scalar bound, so both certificates
remain valid at `max L₂ L₃`.

The depth-two/three transition law gives both opposing zero statements.  If the common strip-mass
envelope forced eventual open-strip zero-freeness, apply it to `dirichletPoly 3` and its mass
certificate, obtaining a cutoff `B`.  The cofinally high depth-three zero theorem supplies a zero
at or above that same `B`, contradiction.  Thus failure is not caused by unequal contour
parameters or unequal mass budgets. `[PROVED HERE]`

## Novelty boundary

Claim only the same-budget Perron-mass blindness and its exact depth-two/three witness.  Individual
finite-carrier mass bounds and the separate zero-transition theorem are prior corpus results.

## Log

- 2026-07-23 — Discovered bottom-up by joining the terminal finite-Dirichlet Perron mass producer
  to the depth-two/three zero-transition theorem.
- 2026-07-23 — Corpus research found no existing same-budget limitation theorem connecting the two.
- 2026-07-23 — Dependency-closed paper proof completed before Lean implementation.
- 2026-07-23 — Formalized the common-budget certificates and explicit failure of the universal
  zero-free inference; exact module check passed without warnings and umbrella import added.
- 2026-07-23 — Post-proof literature search found classical Perron-formula applications,
  zero-distribution work for Dirichlet polynomials, and unrelated Perron methods, but no
  same-envelope strip-mass blindness theorem with the depth-two/three witness.  No scoped
  collision found.
