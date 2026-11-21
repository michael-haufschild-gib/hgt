import GaloisForLFunctions.ThetaCuspSections.StrictEighthSection
import GaloisForLFunctions.ThetaCuspSections.StrictNinthSection
import GaloisForLFunctions.ThetaCuspSections.FiniteRankCriticalCollar
import GaloisForLFunctions.ThetaCuspSections.QuantitativeCriticalCollar
import GaloisForLFunctions.ThetaCuspSections.LogarithmicCriticalCollar
import GaloisForLFunctions.ThetaCuspSections.VinogradovKorobovCriticalCollar
import GaloisForLFunctions.ThetaCuspSections.AllApertureFiniteRankCriterion
import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtom
import GaloisForLFunctions.ThetaCuspSections.FifthEvenSourceRepair
import GaloisForLFunctions.ThetaCuspSections.FifthEvenInheritedLoadBoundary
import GaloisForLFunctions.ThetaCuspSections.FifthEvenOriginObstruction
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSevenKernel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSevenNative
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCoherentRepair
import GaloisForLFunctions.ThetaCuspSections.FifthEvenEndpointBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCoupledEndpointGap
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadContinuation
import GaloisForLFunctions.ThetaCuspSections.CurvatureOfTheXiSusceptibility
import GaloisForLFunctions.ThetaCuspSections.DirectionOfThetaRelativeEntropy

/-!
# Finite signed sections of the theta cusp

Strict positivity of the ninth signed center-mixed Hankel section and its
native successor integral, obtained by retaining the positive aperture tail.
Every finite rank is also strict on a rank-dependent neighborhood of aperture
one half, including apertures inside the critical interval.
The fifth even source admits an entry-preserving zero-flux repair near the
origin and on a cofinal ray. The skipped origin minor forces a positive fifth
load; an explicit scale-seven direction then excludes global source positivity
for every real constant diagonal pair, including every critical aperture.
The full origin positivity region is classified by two sharp load thresholds.
Two coupled loads instead annihilate this witness and repair the origin and
a cofinal tail, preserving every mixed integral and the positive witness energy.
The complete native fifth even block is strictly positive from first-atom
scale five onward, with Gaussian quadratic floor `49/4000`, including the
unique positive compensation zero. One explicit
positive cross-load repairs both the origin and scale seven, preserving every
mixed integral; its weighted scale-seven repair is strict at every positive aperture.
The same cross-load is strict near both endpoints and on a cofinal source ray.
At scale eight it is not positive semidefinite. Its scalar multiples have a
sharp capacity strictly between one half and one: positivity holds below the
capacity, and the boundary matrix is positive semidefinite and singular.
A quartic center-flux profile preserves every fifth even mixed entry and gives
positivity near the origin, near scale eight, and on a cofinal source ray.
Its correction is nonnegative throughout `1/2 ≤ x²`, `0 ≤ x ≤ 3/4`,
where the complete profiled source is positive definite.
At scale thirty-two the quartic repair fails semidefiniteness at every
critical aperture. Its base scalar capacity satisfies `0 < τ < 27/35`;
the literal aperture capacity is `τ/α`, with `67/70 ≤ α ≤ 1`, hence is
at most `70τ/67 < 54/67`. Both capacities have singular semidefinite endpoints.
Truncating the quartic flux at its double zero preserves every mixed entry.
The complete native source pays the quartic cross-load `(3/20)Kq⁴` from scale
seven onward, making the truncated weighted source positive at every positive aperture.
At scale six the truncated quartic source fails semidefiniteness at every critical aperture.
Its base scaling capacity lies strictly between zero and `1000/1251`; the literal aperture
capacity is `τ/α`, with `20/21 ≤ α ≤ 1`, hence is below `350/417`.
Both endpoints are singular positive semidefinite matrices.
Every individual theta atom has a strict fifth even section at reflection scale at least five.
The literal first-atom fifth even tail is positive definite from scale three;
its incomplete-gamma remainder adds a strict reserve at every positive scale.
Every pure-atom tail is a positive radial rescaling of this first-atom tail.
From scale three, that first-atom reserve also pays both ordered cross tails
between atoms one and two; every nonnegative cutoff has a strict leading-pair tail.
The leading tail stays strict after subtracting both first and cubic gamma reserves.
The first gamma correction pays both ordered cross tails between atoms one and three
throughout the same ray.
From scale three, four retained atoms leave normalized Gaussian entry error at most
`1/100000`, hence quadratic error at most `1/20000`.
After radial integration, their complete omitted tail is paid by half the cubic
gamma reserve in the fixed first-atom mass matrix.
The four remaining unequal pairs use the other half of that reserve.
Their exact sum gives positive definite complete fifth even tails at every
nonnegative cutoff. Positive aperture weighting and the fourth odd block
then give the strict ninth section throughout the critical aperture interval.
-/
import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingPairReserve
import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailGammaBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailRateMoments
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPureTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTailMassFloor
import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingTailModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingTailReserve
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTailData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTailCoefficients
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTailModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThirdTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTailData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTailCoefficients
import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTailModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenOtherTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThreeAtomRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenFourAtomRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenIntegratedRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCompleteTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenNativeRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenEffectiveCrossRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadPolynomialEnvelope
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightSourceBounds
import GaloisForLFunctions.ThetaCuspSections.CrossLoadCapacity
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightCapacity
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossInterval
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossCompactEnvelope
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTruncatedQuarticFlux
import GaloisForLFunctions.ThetaCuspSections.FifthEvenQuarticRayModel
import GaloisForLFunctions.ThetaCuspSections.FifthEvenQuarticRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenTruncatedQuarticUpperRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixSourceBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixCapacity
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixApertureCapacity
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoSourceBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossObstruction
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoCapacity
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoApertureCapacity

import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentTail
import GaloisForLFunctions.ThetaCuspSections.ExplicitCurrentCore
import GaloisForLFunctions.ThetaCuspSections.ParabolicCurrentCore
import GaloisForLFunctions.ThetaCuspSections.PoleBudgetCurvature
import GaloisForLFunctions.ThetaCuspSections.FourthTraceZeroGap
import GaloisForLFunctions.ThetaCuspSections.ZeroGapResolventBound
import GaloisForLFunctions.ThetaCuspSections.XiPowerCore
import GaloisForLFunctions.ThetaCuspSections.PowerCurrentCore
import GaloisForLFunctions.ThetaCuspSections.LegendrePolynomialKernel
import GaloisForLFunctions.ThetaCuspSections.ParabolicPolynomialKernel
import GaloisForLFunctions.ThetaCuspSections.PowerPolynomialKernel
import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreDerivatives
import GaloisForLFunctions.ThetaCuspSections.WeightedLegendrePolynomialData
import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreNorms
import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreExterior
import GaloisForLFunctions.ThetaCuspSections.WeightedLegendreKernel
import GaloisForLFunctions.ThetaCuspSections.QuarticLegendreKernel
import GaloisForLFunctions.ThetaCuspSections.TheTenthSectionFromHeightSixtySeven
import GaloisForLFunctions.ThetaCuspSections.QuinticLegendreKernel
import GaloisForLFunctions.ThetaCuspSections.TheSharpCurrentTail
import GaloisForLFunctions.ThetaCuspSections.EvenCauchyBound
import GaloisForLFunctions.ThetaCuspSections.CoupledCurrentTail
import GaloisForLFunctions.ThetaCuspSections.TheEleventhSectionFromHeightSixtySeven
import GaloisForLFunctions.ThetaCuspSections.TheTwelfthSectionFromHeightSixtySeven
import GaloisForLFunctions.ThetaCuspSections.TheThirteenthSectionFromHeightSixtySeven
import GaloisForLFunctions.ThetaCuspSections.TheFourteenthSectionFromHeightSixtySeven
import GaloisForLFunctions.ThetaCuspSections.EverySectionFromItsVerifiedHeight
import GaloisForLFunctions.ThetaCuspSections.GibbsResponse
import GaloisForLFunctions.ThetaCuspSections.RelativeEntropyOfXiTilts
