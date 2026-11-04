import GaloisForLFunctions.ThetaCuspSections.StrictEighthSection
import GaloisForLFunctions.ThetaCuspSections.FiniteRankCriticalCollar
import GaloisForLFunctions.ThetaCuspSections.QuantitativeCriticalCollar
import GaloisForLFunctions.ThetaCuspSections.LogarithmicCriticalCollar
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

/-!
# Finite signed sections of the theta cusp

Strict positivity of the eighth signed center-mixed Hankel section and its
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
Every individual theta atom has a strict fifth even section at reflection scale at least five.
-/
import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingPairReserve
import GaloisForLFunctions.ThetaCuspSections.FifthEvenThreeAtomRemainder
import GaloisForLFunctions.ThetaCuspSections.FifthEvenNativeRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenEffectiveCrossRay
import GaloisForLFunctions.ThetaCuspSections.FifthEvenCrossLoadPolynomialEnvelope
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightSourceBounds
import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightCapacity
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossLoad
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossTail
import GaloisForLFunctions.ThetaCuspSections.FifthEvenPolynomialCrossInterval
