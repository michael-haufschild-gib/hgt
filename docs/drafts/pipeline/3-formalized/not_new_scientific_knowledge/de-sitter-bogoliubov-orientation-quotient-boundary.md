# De Sitter Bogoliubov coefficients expose an unconditional Gamma orientation quotient

- **ID:** `de-sitter-bogoliubov-orientation-quotient-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** M. Sato and H. Suzuki, *On Bogoliubov Transformation of Scalar Wave Functions in De Sitter Space*, arXiv:hep-th/9410092, equation (3.7)
- **Statement:** Every opposite-orientation Gamma quotient `Gamma(z+a)/Gamma(-z+b)` is hypertranscendental, without a separation hypothesis.  The variable Gamma carrier in the type-I global-to-static de Sitter Bogoliubov coefficient is an instance and remains HT after exponential observation.

## Goal

Extract the exact frequency-dependent special-function carrier from a de Sitter change of observer
and promote the strongest reusable theorem to HTGeometry.  The result classifies the observer's
frequency readout, not temporal propagation of the scalar field.

## Gates

- [x] 0 → 1 in-progress: primary-source Bogoliubov formula and affine frequency coordinate located
- [x] 1 → 2 fully-proven: reflection normal form and both collision cases proved
- [x] 2 → 3 formalized: parent theorem, de Sitter instance, readout transport, and source extraction pass
- [ ] 3 → 4 publication-ready: standalone application note not written

## Source relation

Sato--Suzuki equation (3.7) expresses a type-I global de Sitter scalar mode in the static basis.
Up to frequency-independent factors, each branch contains

`Gamma((1 ± nu - i*omega - l - 1/2)/2)
  / Gamma((±nu + l + 1/2 + i*omega)/2)`.

With `z=-i*omega/2`, this is exactly `Gamma(z+a)/Gamma(-z+b)`.  The parameters `a` and `b`
encode the mass branch and angular mode.  Lean formalizes the Gamma carrier and its observation
boundary; it does not formalize the mode expansion or claim a new de Sitter particle-production
formula.

## Exact positive statement

Euler reflection rewrites

`Gamma(z+a)/Gamma(-z+b)`

as a nonzero DA inverse-sine gauge times

`Gamma(z+a) * Gamma(z+1-b)`.

If `a-(1-b)` is not an integer, the two positive-orientation centers give two nonzero orbit
charges.  If it is an integer, they collide, but equal orientations add to charge two instead of
cancelling.  Hence the quotient is HT for all complex `a,b`; the apparent resonance locus is not
an exceptional DA locus.

This no-exception theorem is the significant positive residue: opposite clock orientations are
not a cancellation mechanism after reflection.  A finite scalar-aware differential circuit for
the de Sitter exponential readout must contain an HT non-scalar atom.

## Corpus value

The parent module discharges center-separation hypotheses for every quotient of the same
orientation type.  Its first direct reuse strengthens `GammaReflectionRatioClock`: the reflection
clock `Gamma(-z+a)/Gamma(z+a)` is now unconditionally HT, including the formerly untreated
collision locus.  `RHTower.ZetaChiHypertranscendentalClock` consequently no longer proves the
special `a=1/4` separation arithmetic and now also classifies the reciprocal completed clock.

## Lean certificate

Modules:

- `GaloisForLFunctions.HTGeometry.GammaOrientationQuotientBoundary`
- `GaloisForLFunctions.HTGeometry.DeSitterBogoliubovGammaBoundary`
- `GaloisForLFunctions.HTGeometry.GammaReflectionRatioClock`

Capstones:

- `hypertranscendentalOver_gammaPositiveShiftPairMero_of_integerSeparation`
- `hypertranscendentalOver_gammaPositiveShiftPairMero`
- `gammaOppositeShiftQuotientMero_reflectionNormalForm`
- `hypertranscendentalOver_gammaOppositeShiftQuotientMero`
- `hypertranscendentalOver_deSitterTypeIStaticBogoliubovGammaCarrierMero`
- `hypertranscendentalOver_deSitterTypeIStaticBogoliubovReadoutMero`
- `exists_hypertranscendental_atom_of_deSitterBogoliubovReadoutCircuit`
- `hypertranscendentalOver_gammaReflectionRatioMero`

All audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## RH pressure test

This directly simplifies the live centered-`zetaChi` proof and strengthens its reciprocal
archimedean clock interface.  It establishes that a reflected Gamma normalization cannot lose HT
merely by center collision.  It does not supply a prime source, positivity or sign estimate,
zero-free region, or off-critical-zero exclusion, so it does not by itself prove an RH implication.

## Log

- 2026-07-17 — exact de Sitter coefficient extracted from equation (3.7); unconditional
  orientation-quotient theorem, exponential readout, circuit-source theorem, reflection-clock
  hypothesis discharge, and RH specialization verified with serialized targeted Lean checks.
