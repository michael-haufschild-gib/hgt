# Möbius-contact/Gamma covariant-residue universality law

- **ID:** mobius-contact-gamma-covariant-residue-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of the raw Möbius--Gamma contact-charge formula and the
  all-order Gamma factorial finite-tail/covariant-residue law
- **Statement:** At every finite depth, half the oriented displacement from the raw Möbius contact
  charge to its terminal charge `-2` is exactly Gamma's signed reciprocal factorial pole scale.
  Consequently this contact-charge displacement normalizes every even Gamma factorial finite
  tail to the adjacent intrinsic covariant-residue norm.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `reciprocalGammaFactorialScale`
- `tendsto_gammaFactorialScaledPolygamma_even_finiteTail_eq_neg_covariantResidueNorm`

## Proof

`[PROVED HERE]` The raw depth-`N` contact charge is
`2 (((-1)^N / N!) - 1)`.  Therefore

`(-2 - mobiusGammaContactPartialCharge N) / 2 = (-1)^(N+1) / N!
  = reciprocalGammaFactorialScale N`.

Substitute this exact identity, pointwise in `N`, for the reciprocal factorial scale in the
existing all-order even Gamma finite-tail theorem.  Its limit is unchanged and equals the
negative norm of the grade-`2r+1` covariant top residue at the initial Gamma pole.  No asymptotic
approximation and no computation are used.

## Strict gain over corpus endpoints

The Möbius endpoint identifies a finite contact-charge truncation error but does not connect it to
Gamma's intrinsic residue tower.  The Gamma endpoint normalizes its tail with an internal
factorial scale but does not identify that scale with any arithmetic boundary observable.  Their
closure proves that the observable raw Möbius contact-charge defect is the exact all-order
normalization of Gamma's covariant-residue microscope.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaCovariantResidueUniversalityLaw`
- Main theorem:
  `tendsto_gammaFactorialScaledPolygamma_even_finiteTail_normalizedBy_mobiusContactDefect`
- Source:
  `formal/GaloisForLFunctions/RHTower/MobiusContactGammaCovariantResidueUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaCovariantResidueUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
Möbius contact transgression, reciprocal-Gamma factorial scales, polygamma finite tails, and
covariant residues found no exact collision.  Closest inspected primary source was G. Nemes,
*Error bounds and exponential improvements for the asymptotic expansions of the gamma function
and its reciprocal*, <https://arxiv.org/abs/1310.0166>, which studies Gamma/reciprocal-Gamma
asymptotic remainders but contains no Möbius contact-charge observable or covariant-residue
normalization.  Primary Möbius-function search results concern nilsequence orthogonality rather
than this analytic contact germ and do not meet the theorem's statement.

## Log

- 2026-07-23 — Corpus-defined-symbol scan exposed the shared reciprocal factorial scale.
- 2026-07-23 — Dependency-closed proof completed by exact scale substitution.
- 2026-07-23 — Exact check exposed and corrected the essential orientation sign.
- 2026-07-23 — Corrected theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
