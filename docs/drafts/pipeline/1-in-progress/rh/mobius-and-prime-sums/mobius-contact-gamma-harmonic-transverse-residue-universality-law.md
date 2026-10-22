# Möbius-contact Gamma harmonic transverse-residue universality law

- **ID:** mobius-contact-gamma-harmonic-transverse-residue-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `MobiusGammaContactTransgression`,
  `GammaFactorialHarmonicResidue`, and `GammaFactorialMovingHarmonicResidue`
- **Statement:** The finite Möbius contact-charge defect, refined by the harmonic pole parameter,
  is the exact scale of the first nonzero transverse Gamma Riccati residue: fixed-pole residue is
  contact-charge times digamma, canonical normalization tends to `-2`, and every nonzero moving
  microscope point tends to `-2/x`.

## Goal

Identify arithmetic contact charge not only with the collapsed Gamma boundary scale but with its
first nonvanishing harmonic transverse direction.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `tendsto_gammaFactorialFirstJetDefect_pole_residue`
- `tendsto_normalized_gammaFactorialFirstJetDefect_pole_residue`
- `tendsto_gammaFactorialFirstJetDefect_div_harmonicScale`

## Proof

**[PROVED HERE]** Let `c_n = (-2-mobiusGammaContactPartialCharge n)/2`. Exact contact
transgression gives `c_n = reciprocalGammaFactorialScale n`. Therefore the contact-harmonic scale
`c_n H_n` equals the existing Gamma harmonic microscope scale.

Substitute the first identity into the exact punctured pole residue to obtain
`-2 c_n digamma(n+1)`. Substitute both identities into its normalized pole-depth limit to get
`-2`. Finally substitute the contact-harmonic identity into the moving first-jet Riccati-defect
limit, obtaining `-2/x` at every nonzero microscope point. These are exact rewrites of proven
analytic limits; no computation is used. ∎

## Strict gain over corpus endpoints

Existing contact laws identified the leading factorial scale. Existing harmonic-residue laws
identified the first transverse Gamma direction but had no arithmetic boundary-charge coordinate.
Their closure proves the contact charge controls both the collapsed Riccati boundary and its
canonical nonzero harmonic departure.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaHarmonicTransverseResidueUniversalityLaw`
- Main theorem:
  `mobiusContactGammaHarmonic_completeTransverseResidueUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaHarmonicTransverseResidueUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for reciprocal-Gamma pole expansions, harmonic transverse residues, Riccati defects, and Möbius
partial charges found no exact collision. Closest primary sources:

- L. Fekih-Ahmed, *On the Power Series Expansion of the Reciprocal Gamma Function*,
  <https://arxiv.org/abs/1407.5983>, studies Taylor coefficients of `1/Gamma`; it does not extract
  a moving factorial Riccati first-jet defect or normalize it by an arithmetic contact charge.
- G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, <https://arxiv.org/abs/1310.0166>, concerns large-argument
  asymptotics and Stokes improvement, not moving negative-integer pole microscopes.
- S. Inoue, *Some explicit formulas for partial sums of Möbius functions*,
  <https://arxiv.org/abs/1805.05015>, treats arithmetic-progressions and number-field Möbius sums,
  not Gamma Riccati residues or harmonic microscopes.

## Log

- 2026-07-23 — whole-scale scan exposed the harmonic refinement of the contact defect.
- 2026-07-23 — dependency-closed proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
