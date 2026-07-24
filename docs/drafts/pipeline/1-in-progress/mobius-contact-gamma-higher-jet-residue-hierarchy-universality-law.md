# Möbius-contact Gamma higher-jet residue hierarchy universality law

- **ID:** mobius-contact-gamma-higher-jet-residue-hierarchy-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `MobiusGammaContactTransgression`,
  `GammaFactorialSecondJetHarmonicResidue`, `GammaFactorialThirdJetHarmonicResidue`, and
  `GammaFactorialExponentialEnvelopeEscape`
- **Statement:** The finite Möbius contact defect generates the complete proven higher-jet
  transverse hierarchy: second-jet and projective-curvature residues occur at contact-harmonic
  scale, Schwarzian residue at its square, and logarithmic/exponential-reciprocal discriminants at
  squared contact-factorial scale, with exact nonzero reciprocal profiles.

## Goal

Extend arithmetic contact normalization from first-jet Riccati departure to every currently proved
second/third-jet Gamma differential hypersurface.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `mobiusGammaContactPartialCharge_eq`
- `tendsto_gammaFactorialSecondJetDefect_div_harmonicScale`
- `tendsto_gammaFactorialSecondJetProjectiveDefect_div_harmonicScale`
- `tendsto_gammaFactorialThirdJetProjectiveDefect_div_harmonicScale_sq`
- `tendsto_gammaFactorialLogCurvatureDiscriminant_div_factorialScale_sq`
- `tendsto_gammaFactorialExponentialEnvelopeDefect_div_factorialScale_sq`

## Proof

**[PROVED HERE]** Put `c_n=(-2-contactCharge_n)/2`. Exact transgression gives
`c_n=reciprocalGammaFactorialScale n`, hence `c_n H_n=gammaHarmonicMicroscopeScale n`.
Substitute these two identities, and their squares, into the five established higher-jet limits.
The resulting contact-normalized limits are respectively `6/x^2`, `2/x^3`, `-6/x^4`,
`-4 pi^2/x^4`, and `-4 pi^2/x^10`. All are nonzero for `x≠0`, so the contact defect records
genuine transverse escape at each layer. No computation is used. ∎

## Strict gain over corpus endpoints

Existing higher-jet laws used two formally separate Gamma scales and did not identify their
arithmetic origin. Contact transgression had reached only selected lower layers. The closure
organizes all proved second/third-jet hypersurface escapes into one arithmetic scale hierarchy.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.MobiusContactGammaHigherJetResidueHierarchyUniversalityLaw`
- Main theorem:
  `mobiusContactGammaHigherJet_completeResidueHierarchyUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/MobiusContactGammaHigherJetResidueHierarchyUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for Gamma Schwarzian/Riccati higher jets, negative-integer harmonic residues, jet discriminants,
and exponential-reciprocal envelopes found no exact collision. Closest primary sources:

- L. Fekih-Ahmed, *On the Power Series Expansion of the Reciprocal Gamma Function*,
  <https://arxiv.org/abs/1407.5983>, studies coefficient asymptotics of `1/Gamma`, not a hierarchy
  of differential hypersurface residues at moving poles.
- G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, <https://arxiv.org/abs/1310.0166>, treats large-argument
  expansions, not contact-normalized second/third jet discriminants.
- M. Chuaqui, P. Duren, and B. Osgood, *Schwarzian Derivative Criteria for Valence of Analytic and
  Harmonic Mappings*, <https://arxiv.org/abs/math/0607067>, studies Schwarzian valence criteria,
  not Gamma pole microscopes or arithmetic residue scales.

## Log

- 2026-07-23 — complete `reciprocalGammaFactorialScale` scan exposed higher-jet residue hierarchy.
- 2026-07-23 — dependency-closed proof completed.
- 2026-07-23 — exact Lean proof passed warning-free and module wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
