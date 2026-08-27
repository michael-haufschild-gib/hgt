# Reflected bi-heat signed three-scale receiver cone

- **ID:** RBH-S3S
- **Stage:** 3-formalized
- **Type:** COMPLETE THREE-RATE SIGNED RECEIVER CLASSIFICATION
- **Parent:** RBH-STS / RBH positive-matrix aperture classification
- **Frontier-map policy:** read only

## Frozen conjecture

For

`F_{a,b,c}(t)=a sinh(t)+b sinh(2t)+c sinh(3t)`,

prove the exact factorization

`F(t)=sinh(t) Q(cosh(t))`,

where `Q(u)=4c u²+2b u+(a-c)`.  Classify `t=0` as the only real zero iff
`Q` is strictly positive or strictly negative on `(1,∞)`.  Express the result
semialgebraically by reusing `quadraticPositiveOnOneCondition` for `Q` or `-Q`.

Required new infrastructure:

1. exact classification of a real quadratic being nonzero on `(1,∞)` as the
   union of its positive and negative half-line cones;
2. converse sign constancy from continuity/intermediate value;
3. physical factorization for weighted RBH gaps at `x`, `x²`, `x³`;
4. RH equivalence for every coefficient triple in the cone.

## Corpus basis

- RBH-STS exact two-scale `sinh/cosh/arcosh` workflow.
- `ThetaCuspHawkingParikhWilczekQuadraticHalfLineReceiverCone` complete strict
  positivity classifier `quadratic_pos_on_one_iff`.
- Corpus intermediate-value proofs (`intermediate_value_Icc` and primed form).
- Multiplicity-leading RBH arbitrary-aperture norm identities.

## Expected new insight

Three signed commensurate aperture rates are governed exactly by the already
formalized quadratic half-line geometry from the independent PW-B route.  This
would be first explicit cross-route transfer: PW-B quadratic cone becomes the
complete RBH three-rate cancellation cone.

## Lean theorem package

Module:
`GaloisForLFunctions.RHTower.ReflectedBiHeatSignedThreeScaleReceiverCone`

- `quadratic_ne_zero_on_one_iff`
- `reflectedBiHeatSignedThreeScaleReporter_factor`
- `reflectedBiHeatSignedThreeScaleWallSelective_iff`
- `reflectedBiHeatWeightedPowerApertureGap_eq_sinh`
- `reflectedBiHeatSignedThreeApertureGap_eq_reporter`
- `reflectedBiHeatSignedThreeApertureGap_eq_zero_iff`
- `riemannHypothesis_iff_reflectedBiHeatSignedThreeApertureGap_eq_zero`
- `reflectedBiHeatSignedThreeScaleWallSelective_neg_three_zero_one`
- `riemannHypothesis_iff_reflectedBiHeatSignedNegThreeZeroOneApertureGap_eq_zero`

## Exact new insight

The conjectured cross-route transfer is exact:

`F_{a,b,c}` is wall-selective iff the PW-B quadratic cone contains either
`(4c,2b,a-c)` or its negative.  The new general theorem
`quadratic_ne_zero_on_one_iff` proves a quadratic nonvanishing on `(1,∞)` must
have one strict sign there and converts that fact to the previously formalized
semialgebraic positivity chambers.

The aperture-normalization theorem is stronger than the three-scale case: for
every natural `n`, the gap at `x^n`, weighted by `x^(n/2)`, equals the common
nonzero multiplicity coefficient times `2 sinh(n t)`.  This exposes the full
commensurate-scale Chebyshev hierarchy for later finite-rate classification.

The signed boundary ray `(-3,0,1)` gives
`sinh(3t)-3sinh(t)=4sinh(t)^3`; its physical three-aperture balance is exactly RH.

## Novelty audit (provisional, 2026-08-27)

No checked heat-flow/RH, generalized Descartes, or hyperbolic-polynomial source
states this RBH/PW-B cone transfer, the all-natural-power aperture normalization,
or the signed `(-3,0,1)` RH receiver.  Priority remains provisional pending
expert review.

Primary sources checked:

- arXiv:1904.12438, Riemann-`xi` heat flow and de Bruijn--Newman constant
- arXiv:2107.10002, generalized Descartes geometry for real-exponent polynomials
- arXiv:2304.02307, Descartes rules for hyperbolic polynomials

## Verification

- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/ReflectedBiHeatSignedThreeScaleReceiverCone.lean`
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.ReflectedBiHeatSignedThreeScaleReceiverCone`
- Seven principal theorems depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.
- Umbrella import wired in `GaloisForLFunctions/RHTower.lean`.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration.

## Status

- Mandatory corpus and primary-literature searches complete.
- Paper proof dependency-closed.
- Lean proof, direct check, targeted build, and axiom audit complete.
- Exact three-scale signed receiver cone formalized.
