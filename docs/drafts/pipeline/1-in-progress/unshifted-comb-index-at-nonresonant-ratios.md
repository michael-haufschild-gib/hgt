# Unshifted comb index at nonresonant ratios

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** A94.
- **Statement:** At every integer ratio `Q≥2`, the eventual unshifted comb
  index on `(N,QN]` lies between the negative rank and rank plus nullity
  at aperture `log Q/2`. Equality holds when nullity vanishes.

## Connection

Robust comb index transfer, mean-only Schur errors, and finite-aperture nullity
growth suggest exact index convergence away from resonances.

Required bridges:

1. The restricted index is right-locally constant at a nonresonant aperture.
   Put smaller form domains in one ambient weighted Fourier space. If
   extra negative directions persisted down to the limiting aperture,
   choose unit vectors orthogonal to its finite negative space. Compactness
   of the Birman–Schwinger operator supplies a nonzero nonpositive limit
   in that orthogonal complement. Absence of a null mode excludes it.
   `SuzukiGroundEnergyContinuity` supplies the existing no-boundary-escape
   mechanism for aperture limits.
   `SignedArithmeticEnergyIncidence/TheRestrictedWeilFormIsCompactlyNegative` supplies bounded weak-to-strong
   compact transfer and lower semicontinuity. Exact unit normalization
   prevents disappearance even when the limiting energy is zero.
   The sharper candidate is an exact right-hand jump: on some interval
   immediately above `a`, the index equals `negativeRank(a,E)+nullity(a,E)`.
   Non-radiation gives the lower bound; compactness excludes further modes.
2. Preserve an arbitrarily small ratio loss when padding blocks. For block
   scale `R`, use `(Q−1)R+1` blocks and sufficiently large block size, giving
   outer ratio `Q+1/R`.
3. Charge approximation errors to block means.
   A small positive energy shift stays below the next positive eigenvalue,
   bounding every unshifted negative comb subspace by the continuum index.
   The mean-only error already makes the block map injective on every
   negative subspace; no extra residual mass floor is needed.
4. Smooth finite negative families sample into the original ratio window.
   A translated sampling grid at `⌊N/3⌋` and strict support margins allow
   zero extension from the existing sampling theorem.
   `SuzukiRayleighInfimum.denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector`
   supplies density in the full form norm, and `CCMZetaWeilSmoothIdentity`
   identifies mixed CCM forms with `zetaZeroConfig.W` exactly.

Passed Lean:

- `SignedArithmeticEnergyIncidence/UnitNonpositiveLimitsDoNotVanish`:
  unit weak limits remain nonzero even for vanishing upper energy bounds.

- `ArithmeticContinuationAndCriticalEnergy/NonpositiveRightApertureLimits`:
  strong physical limits retain support in the limiting aperture.

- `ArithmeticContinuationAndCriticalEnergy/TheRightApertureIndexIncludesExactlyTheNullModes`:
  exact right-hand index jump and constancy at nonresonant apertures.

- `ArithmeticContinuationAndCriticalEnergy/NonresonantWeilIndexSurvivesPositiveEnergyShifts`:
  simultaneous aperture enlargement and positive mass shift capture exactly
  the original rank plus nullity.

- `HTGeometry/FiniteGramsOfAnOperator`: finite Gram index is bounded by
  operator index, and a negative-space basis attains equality.

- `RHTower/FiniteSmoothWeilGramsAndRestrictedIndex`: full index capture
  by a finite smooth family, using form-core density.

- `AbsoluteGeometryOfSpecZ/ShiftedSmoothPacketGrams`: exact real mass
  polarization and identification with the native shifted Weil Gram.

Written, uncompiled:

- `HodgeTheoryOfAFixedPart/TightBlockTransferSpendsOnlyMeanMass`:
  arbitrarily fine fixed block scales and padding with ratio loss `1/R`.
- `AbsoluteGeometryOfSpecZ/ShiftedBoundedPacketIndexFitsTheAperture`:
  simultaneous smoothing and centering bound every shifted bounded-packet
  Gram by the restricted index at any strictly wider aperture.
- `HodgeTheoryOfAFixedPart/TheApertureIndexCountsNoExtraZeros`:
  smooth-core density bounds the completed aperture index by the zero count.
- `HodgeTheoryOfAFixedPart/SmoothRealPacketsCaptureTheApertureIndex`:
  realification retains smoothness and strict support while capturing the index.

- `AbsoluteGeometryOfSpecZ/PacketMassGrams`: exact physical-mass Gram
  and mass-shifted nested quadratic identity.

- `HodgeTheoryOfAFixedPart/UnshiftedCombIndexFitsEveryWiderAperture`:
  complex tight-block transfer and the nonresonant eventual upper bound.

- `HodgeTheoryOfAFixedPart/SmoothSamplesFitTheOriginalRatio`:
  scalar sampling convergence at scale `⌊N/3⌋` in the original window.

`HodgeTheoryOfAFixedPart/TheUnshiftedCombIndexAtItsOwnAperture` assembles
finite Gram sampling, common translation, and both index bounds. Full draft
is written; remaining Lean checks are pending. Supports are not separately
counted contributions.
