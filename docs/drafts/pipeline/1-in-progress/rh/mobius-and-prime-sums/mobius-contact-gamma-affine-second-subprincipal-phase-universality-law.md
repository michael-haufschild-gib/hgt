# Möbius-contact Gamma affine/second-subprincipal phase universality law

- **ID:** mobius-contact-gamma-affine-second-subprincipal-phase-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `MobiusGammaContactTransgression` and
  `GammaAffineSecondSubprincipalPhaseSeparationUniversalityLaw`
- **Statement:** In every weighted Gamma source with cancelled principal and first-partial
  channels, the finite Möbius contact defect is the exact moving-pole coordinate of the affine
  order--energy phase; any surviving second-subprincipal boundary forces nonlinear degree and
  cofinal exact native/covariant order, so the contact-affine and nonlinear phases are disjoint.

## Goal

Give arithmetic contact charge a structural role in complete Gamma pole-profile phase separation,
beyond normalization of individual limits.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `gammaAffineSecondSubprincipal_phaseSeparationUniversalCertificate`

## Proof

**[PROVED HERE]** Replace `reciprocalGammaFactorialScale branch` in the moving-pole affine
order--energy phase by `(-2-mobiusGammaContactPartialCharge branch)/2`. Exact contact
transgression proves the two phase predicates equivalent branch by branch.

Apply the existing phase-separation certificate. Its affine branch transports through this
equivalence to the contact-normalized phase. Its second-subprincipal branch already supplies degree
at least two and cofinal exact meromorphic order on native and covariant realizations. The existing
boundary-symbol exclusion proves disjointness. No computation is used. ∎

## Strict gain over corpus endpoints

The earlier phase theorem used a formal factorial coordinate; contact laws normalized particular
Gamma limits. Their closure makes an arithmetic finite boundary-charge defect the coordinate that
selects the entire affine order--energy chamber against the nonlinear second-subprincipal chamber.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaAffineSecondSubprincipalPhaseUniversalityLaw`
- Main theorem:
  `gammaMobiusContactAffineSecondSubprincipal_phaseSeparationUniversality`
- Exact predicate bridge:
  `gammaMobiusContactAffineOrderEnergyPhase_iff`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaAffineSecondSubprincipalPhaseUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for Gamma weighted-jet pole profiles, affine versus second-subprincipal boundary phases,
meromorphic-order separation, and Möbius contact charge found no exact collision. Closest primary
sources concern ordinary Gamma asymptotics:

- G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, <https://arxiv.org/abs/1310.0166>, studies asymptotic expansions
  and Stokes terms, not weighted jet-polynomial phase classification.
- L. Fekih-Ahmed, *On the Power Series Expansion of the Reciprocal Gamma Function*,
  <https://arxiv.org/abs/1407.5983>, studies Taylor coefficients, not affine/nonlinear
  second-subprincipal exclusion or arithmetic contact coordinates.

## Log

- 2026-07-23 — exact shared-scale scan connected contact transgression to Gamma profile phase
  separation.
- 2026-07-23 — dependency-closed proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
