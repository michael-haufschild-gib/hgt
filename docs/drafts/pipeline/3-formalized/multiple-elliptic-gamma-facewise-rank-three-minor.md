# Universal raw-face and rank-three-minor laws

- **ID:** `multiple-elliptic-gamma-facewise-rank-three-minor`
- **Stage:** 3-formalized
- **Type:** THEOREM / FACEWISE HYPERTRANSCENDENCE / RAW DIFFERENTIAL MATROID
- **Scientific status:** `[PROVED] [APPLICATION + BRIDGE]`

## Exact statement

Let `J` be any deletion face of a finite upper-half-plane period family. If the periods surviving
`J` contain two distinct entries which, together with the unit period, are linearly independent
over `Q`, then both:

1. the genuine raw multiple elliptic-gamma function on `J`; and
2. its logarithmic derivative

are hypertranscendental over `C(z)`. Rational dependencies among all other surviving periods are
allowed.

Under integral independence of the unit period and the full period family:

1. all external translates of all raw face functions retaining at least two periods are jointly
   differentially independent over `C(z)`;
2. the complete raw hierarchy has exactly the same differential matroid as its coordinatewise
   logarithmic-derivative hierarchy;
3. a translated raw face function is differentially algebraic iff fewer than two periods survive.

## Proof

The rank-three statement specializes the existing minor theorem to the surviving face family.
For the hierarchy statement, translation commutes with derivation and division, so the
logarithmic derivative of every translated raw coordinate is its correspondingly labelled
logarithmic coordinate. Complete face separation makes those labels injective. Coordinatewise
raw/log differential-matroid invariance then transfers full hierarchy independence and the exact
phase boundary from logarithmic to raw coordinates.

## Verification

- Module:
  `formal/GaloisForLFunctions/HTGeometry/MultipleEllipticGammaFacewiseRankThreeMinor.lean`
- Theorem:
  `multipleEllipticGammaFace_rankThreeMinor_hypertranscendence`
  `multipleEllipticGammaRawFaceFamily_differentialIndependent_rationalBase`
  `multipleEllipticGammaRawFaceFamily_differentialMatroid_eq_logFaceFamily`
  `multipleEllipticGammaRawFacePacket_differentialAlgebraic_iff`

No project axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration is introduced.
