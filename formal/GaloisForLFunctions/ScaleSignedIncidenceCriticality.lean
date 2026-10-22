/-
Scale-Signed Incidence Criticality: the resolution calculus of readings of the critical
arithmetic form.

A reading is a map `r : D → O` from data to the observables a method uses; its shadow at `d` is the
set of data with the same reading, and the resolution limit of a real invariant `I` is the supremum
of `I` over the shadow, which is exactly the best bound any method reading `r` can certify. The
bundled modules prove:

- the general calculus: the collapse–resolution dichotomy, `certifies_iff_resolutionLimit_le`,
  monotonicity under refinement and joins, and the dual resolution floor;
- blindness of bounded-aperture sign certificates: on tempered zero configurations the width
  `sup |Re ρ - 1/2|` has resolution limit `1/2` and floor `0` under aperture positivity at any
  aperture, coercivity level, monotone change of unit or family, and the depth of the two-parameter
  lattice family is the complete invariant of the dilation action yet has limit `1/2` under a single
  aperture certificate;
- the square-root precision law: a level-`η` certificate at scale `L` resolves depth only down to
  `min (1/2) (arcosh(1 + η/(2L))/L)`, which is at most `√(η/L³)`, and the depth equals the
  infimum of the rates `β` for which the deficit is `O(e^{2βa})` in the aperture `a`;
- the hiding laws: an isolated off-line pair cannot sustain the floor, mass buys aperture only
  logarithmically, and sub-lattice aliasing is free exactly below half the spacing;
- positive recipes from magnitudes: two aliasing bands determine the lattice depth in closed form,
  three bands determine it with unknown on-line mass, and one aperture doubling determines the
  depth of a single pair; the band-pair reading is faithful (limit equals the depth);
- the refutation calculus: a single certificate radius, aperture or membership bit can refute,
  while confirmation on the incidence face needs every prime power; RH is equivalent to no
  bounded-radius certificate refuting membership of the von Mangoldt weight in the full Weil cone;
- reduction laws: RH follows from aperture positivity of the zeta configuration along any
  unbounded set of apertures, or from weight-aperture positivity of `Λ` along any unbounded set of
  radii, whereas no node set missing a prime power is zero-pole positive;
- rate readings: for convex deficits the growth-rate reading on a cofinal aperture set has the same
  shadows as on all apertures, while on a bounded aperture range it certifies no rate at all.

The statements are unconditional. RH appears only as an equivalence or as the conclusion of the
sufficiency theorems, whose premises are the positivity certificates along unbounded aperture or
radius sets; those premises are not proved here.
-/
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheResolutionLimitOfAReading
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheApertureCertificateIsBlindInEveryUnit
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.RefutationIsFiniteConfirmationIsNot
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheSquareRootPrecisionLaw
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheDepthIsTheCompleteDilationInvariant
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHidingLaws
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TwoAliasingBandsDetermineTheDepth
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThreeBandsDefeatTheMass
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheMagnitudePairIsFaithfulWhereTheSignIsBlind
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.SparseAperturesSufficeAndTheIncidenceFaceDoesNot
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheRateIsACofinalInvariant
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheBoundedApertureRateCertifiesNothing
