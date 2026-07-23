# Generic-spectrum functional-equation fracture universality law

- **ID:** generic-spectrum-functional-equation-fracture-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of finite DSS spectral genericity and function-field weighted
  reciprocal spectral-closure completeness
- **Statement:** In every characteristic-zero field, a nonempty finite spectrum whose complete
  elementary-symmetric coordinate packet is algebraically independent over `ℚ` cannot be closed
  under `ω ↦ q / ω` for any rational constant weight `q`.  In particular, the universal generic
  secular spectrum in the fraction field of its polynomial coordinate ring has no rationally
  weighted reciprocal functional equation.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `spectrum_esymm_algIndep`
- `functionField_spectralClosure_iff_esymm_FE`
- `functionField_spectralClosure_iff_bounded_esymm_FE`
- `multiset_eq_of_esymm_eq`

## Proof

`[PROVED HERE]` First generalize weighted reciprocal spectral-closure completeness from `ℂ` to an
arbitrary field.  If a nonempty `n`-point spectrum is closed under `ω ↦ q / ω`, its top symmetric
coordinate satisfies `e_n = q^n e_n⁻¹`, hence `e_n² = q^n`.  Algebraic independence of the
complete symmetric packet makes `e_n` transcendental over `ℚ`, while that displayed equation makes
it algebraic, a contradiction.  For the universal generic spectrum, evaluation of each elementary
symmetric polynomial at the fraction-field images of the variables is exactly its multiset
symmetric coordinate; `spectrum_esymm_algIndep` survives the injective fraction-field map and
discharges the abstract hypothesis.  No computation is used.

## Strict gain over corpus endpoints

The DSS theorem proves genericity but says nothing about functional equations.  Function-field
closure classifies reciprocal pairing but allows highly constrained spectra.  Their closure gives
an exact incompatibility boundary: a fixed rational functional-equation weight forces algebraic
dependence already in the top coefficient, so full finite DSS genericity and reciprocal
function-field closure are mutually exclusive.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.GenericSpectrumFunctionalEquationFractureUniversalityLaw`
- Main theorems:
  `algebraicallyIndependentSpectrum_not_fixedRationalWeightedReciprocal`,
  `genericSecularSpectrum_not_fixedRationalWeightedReciprocal`
- Source:
  `formal/GaloisForLFunctions/RHTower/GenericSpectrumFunctionalEquationFractureUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/GenericSpectrumFunctionalEquationFractureUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for generic
spectra, algebraically independent elementary-symmetric coordinates, reciprocal and
self-reciprocal polynomials, and weighted functional equations found work on self-reciprocal
polynomial classes and symmetric zero sets, but no arbitrary characteristic-zero-field fracture
theorem and no generic secular fraction-field law of this form.  Closest inspected primary
sources:

- L. Fel, *Self-Dual Symmetric Polynomials and Conformal Partitions*,
  <https://arxiv.org/abs/math/0111155>.
- S. Mattarei and M. Pizzato, *Generalizations of self-reciprocal polynomials*,
  <https://arxiv.org/abs/1609.07677>.
- R. S. Vieira, *Polynomials with symmetric zeros*,
  <https://arxiv.org/abs/1904.01940>.

## Log

- 2026-07-23 — Terminal cross-folder scan exposed finite spectral genericity versus
  function-field spectral closure.
- 2026-07-23 — Common arbitrary-field carrier constructed; dependency-closed proof completed.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
