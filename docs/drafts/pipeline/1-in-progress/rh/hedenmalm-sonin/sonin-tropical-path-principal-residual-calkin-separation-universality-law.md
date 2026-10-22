# Sonin Tropical-Path / Principal-Residual Calkin Separation Universality Law

- **ID:** LAW447
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean target)
- **Source:** Lean-corpus synthesis of
  `SoninPrincipalShellResidual.lean` and
  `SoninTropicalCalkinPathUniversalityLaw.lean`
- **Statement:** Every genuine finite Sonin Gram path is separated modulo compact operators from
  both the canonical one-scale principal-shell residual and its positive residual energy.

## Goal

Identify the exact ideal-theoretic boundary between tropical path memory and the arithmetic
principal-shell correction.

## Gates

- [x] 0 → 1 in-progress: common Calkin quotient and opposite compactness classes found
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized:
  `soninTropicalPath_principalResidual_calkinSeparationUniversality`;
  `lake env lean GaloisForLFunctions/RHTower/SoninTropicalPathPrincipalResidualCalkinSeparationUniversalityLaw.lean`
  clean; imported by `GaloisForLFunctions/RHTower.lean`
- [ ] 3 → 4 publication-ready: pending standalone exposition and external novelty review

## Statement

For every positive cutoff `a`, every scale `p>1`, and every finite composable Sonin scale path
`P`:

- `evenSoninPrincipalShellResidual a p hp` is compact;
- `evenSoninPrincipalShellEnergy a p hp` is compact and has nonnegative quadratic form;
- `P.operator a` is not compactly equivalent to either operator.

Thus the residual and its energy vanish in the Calkin quotient, while every tropical path word
represents a nonzero Calkin class.

## Paper proof

The principal-shell residual theorem makes the residual compact.  Compactness is stable under
composition, giving compact residual energy; its quadratic form is nonnegative by the adjoint
square identity.

The tropical path certificate says every path word is noncompact.  If a path word were compactly
equivalent to either compact residual operator, compactness invariance under compact congruence
would make the path word compact, contradiction.  The argument is uniform in path, scale, and
positive cutoff. `[PROVED HERE]`

## Novelty boundary

Claim only the cross-mechanism Calkin separation.  Compactness/positivity of the residual channels
and noncompactness/minimum classification of path words are prior corpus results.

## Log

- 2026-07-23 — Discovered bottom-up from the shared `CompactOperatorEq` interface and opposite
  compactness classes.
- 2026-07-23 — Corpus research found no theorem separating all tropical path words from both
  principal residual channels.
- 2026-07-23 — Dependency-closed paper proof completed before Lean implementation.
- 2026-07-23 — Formalized simultaneous compactness, positivity, and both strict Calkin
  separations; exact module check passed without warnings and umbrella import added.
- 2026-07-23 — Post-proof literature search found generic Calkin-algebra compact-perturbation
  theory and Gram compactness results, but no Sonin tropical-path/principal-residual separation.
  No scoped collision found.
