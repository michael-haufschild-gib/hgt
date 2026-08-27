# Reflected bi-heat signed two-scale receiver cone

- **ID:** RBH-STS
- **Stage:** 3-formalized
- **Type:** EXACT SIGNED RECEIVER CLASSIFICATION / POSITIVE SURVIVOR
- **Parent:** RBH positive-matrix aperture classification
- **Frontier-map policy:** read only

## Frozen conjecture

For the normalized two-scale reporter

`F_{a,b}(t) = a sinh(t) + b sinh(2t)`,

classify exactly when its only real zero is the self-dual wall `t=0`.  Prove

`(∀ t, F_{a,b}(t)=0 ↔ t=0)` iff

- `b=0` and `a≠0`, or
- `b≠0` and `b(a+2b)≥0`.

Bridge this exact cone to physical multiplicity-leading RBH diagonal gaps at
commensurate apertures `x` and `x²`.  The weighted physical gap should factor as

`2 |C(rho)|² F_{a,b}(log(x)(Re(rho)-1/2))`.

Deduce an exact RH receiver for every coefficient pair in the cone and exhibit
the genuinely signed boundary point `(a,b)=(-2,1)`.

## Corpus basis

- `ReflectedBiHeatPositiveMatrixApertureClassification`: exact arbitrary-aperture
  leading-jet norm laws and positive-matrix receiver cone.
- `Real.sinh_two_mul`, `Real.one_lt_cosh`, `Real.cosh_arcosh`, and
  `Real.arcosh_pos` in the active Lean toolchain.
- Corpus exponential-mode/Vandermonde results identify signed cancellation as
  the remaining finite receiver problem.

## Paper proof

Factor

`F_{a,b}(t)=sinh(t)(a+2b cosh(t))`.

Inside stated cone, second factor cannot vanish away from zero: after multiplying
by `b`, it equals

`b(a+2b)+2b²(cosh(t)-1)>0` for `t≠0`.

Conversely, if `b(a+2b)<0`, then `c=-a/(2b)>1`; taking
`t=arcosh(c)>0` makes second factor zero and constructs a non-wall zero.  Cases
`b=0` and `(a,b)=(0,0)` are immediate.

## Novelty status

Provisional `[NEW]`: checked heat-flow/RH and generalized Descartes literature
does not state this exact physical RBH two-aperture cone or its signed
`(-2,1)` RH receiver.  Priority requires expert review.

Primary sources checked:

- arXiv:1904.12438, heat-flow evolution of Riemann `xi` and the
  de Bruijn--Newman constant
- arXiv:2107.10002, generalized Descartes sign geometry for real-exponent
  polynomials
- arXiv:2304.02307, Descartes sign rules for hyperbolic polynomials

## Lean theorem package

Module:
`GaloisForLFunctions.RHTower.ReflectedBiHeatSignedTwoScaleReceiverCone`

- `reflectedBiHeatSignedTwoScaleReporter_factor`
- `reflectedBiHeatSignedTwoScaleWallSelective_iff`
- `reflectedBiHeatSignedTwoApertureGap_eq_reporter`
- `reflectedBiHeatSignedTwoApertureGap_eq_zero_iff`
- `riemannHypothesis_iff_reflectedBiHeatSignedTwoApertureGap_eq_zero`
- `reflectedBiHeatSignedTwoScaleWallSelective_neg_two_one`
- `riemannHypothesis_iff_reflectedBiHeatSignedNegTwoOneApertureGap_eq_zero`

## Exact new insight

Entrywise nonnegativity is sufficient but not necessary for an RBH aperture
receiver.  The complete two-rate cone contains signed boundary rays.  In
particular

`sinh(2t)-2sinh(t)=2sinh(t)(cosh(t)-1)`

has no non-wall real zero, so a negative first-aperture coefficient can be
compensated by a positive squared-aperture coefficient without introducing a
false balance.  Outside the cone, the proof constructs the exact false-balance
location `arcosh(-a/(2b))`.

This closes signed cancellation completely for two commensurate diagonal
aperture scales.  Three or more effective rates and general collision-grouped
matrix products remain.

## Verification

- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/ReflectedBiHeatSignedTwoScaleReceiverCone.lean`
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.ReflectedBiHeatSignedTwoScaleReceiverCone`
- Five principal theorems depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Umbrella import wired in `GaloisForLFunctions/RHTower.lean`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Status

- Mandatory corpus and primary-literature searches complete.
- Paper proof dependency-closed.
- Lean proof, direct check, targeted build, and axiom audit complete.
- Exact two-scale signed cone formalized.
