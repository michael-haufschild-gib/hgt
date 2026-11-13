import GaloisForLFunctions.ZeroConfigurationGeometry.AbscissaLaws.TheAbscissaLawsOfAZeroConfiguration
import GaloisForLFunctions.ExactEventTheory.IntegrableDefectsHaveDecayingBoundary
import GaloisForLFunctions.ExactEventTheory.TentPairingsOfIntegrableDefects
import GaloisForLFunctions.ExactEventTheory.TentRecurrenceOfIntegrableDefects
import GaloisForLFunctions.ExactEventTheory.IntegrableDefectsVanishInTheUnitGap
import GaloisForLFunctions.EulerFETransportTheory.IntegrableDefectsForceIntegerSupport
import GaloisForLFunctions.EulerFETransportTheory.IntegrableFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.EulerFETransportTheory.ContinuousPrimeMeasuresAreNotRigidUnderFiniteDefects
import GaloisForLFunctions.EulerFETransportTheory.TheBoundaryPreservesDefectEnergy
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsHaveCanonicalBoundaries
import GaloisForLFunctions.EulerFETransportTheory.TheDefectHasAUnitaryMellinSource
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsAreLaplaceTransforms
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsConvergeToTheirBoundary
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsObeyTheTentIdentity
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyTentErrorsVanish
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsRetainAtomicRecurrence
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsVanishInTheUnitGap
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsForceIntegerSupport
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsHaveNoBoundaryResidues
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsPreserveAtomicResidues
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyRigidityAnnihilatesTheDefect
import GaloisForLFunctions.EulerFETransportTheory.LocalThetaDataDetermineTheDefect
import GaloisForLFunctions.EulerFETransportTheory.IntegrableRigidityAnnihilatesTheDefect
import GaloisForLFunctions.EulerFETransportTheory.TheGaussianDefectDeterminesTheCausalTail
import GaloisForLFunctions.EulerFETransportTheory.TheCausalGaussianDefect
import GaloisForLFunctions.EulerFETransportTheory.TheGaussianRateMeasureIsLocallyVisible
import GaloisForLFunctions.EulerFETransportTheory.TheGaussianDefectDeterminesCausalMeasures
import GaloisForLFunctions.EulerFETransportTheory.AtomicEulerCorrectionCannotRepairGaussianSurgery
import GaloisForLFunctions.EulerFETransportTheory.SignedEulerCorrectionCannotRepairGaussianSurgery
import GaloisForLFunctions.EulerFETransportTheory.TheNormalizedHeightReflection
import GaloisForLFunctions.EulerFETransportTheory.TheWholeQuadrantCannotSupportReturns
import GaloisForLFunctions.EulerFETransportTheory.TheFinitePartOfTheGaussianPrimeCurrent
import GaloisForLFunctions.EulerFETransportTheory.GaussianRenormalizationAtZeros
import GaloisForLFunctions.EulerFETransportTheory.ThePrimeCurrentReadsTopMultiplicity
import GaloisForLFunctions.EulerFETransportTheory.TheArchimedeanDampingErrorIsUniform
import GaloisForLFunctions.EulerFETransportTheory.TheFullGaussianCurrentAtEscapingHeights
import GaloisForLFunctions.EulerFETransportTheory.OnlyExceptionalGaussianModesRemain
import GaloisForLFunctions.EulerFETransportTheory.ThePrimeCurrentPassesAcrossDyadicWindows
import GaloisForLFunctions.EulerFETransportTheory.ThePrimeCurrentPassesAtInverseHeight
import GaloisForLFunctions.EulerFETransportTheory.TheHeadDoesNotChangeTheInfiniteRoughMean
import GaloisForLFunctions.EulerFETransportTheory.TheGaussianRoughMeanSurvivesVanishingDamping
import GaloisForLFunctions.EulerFETransportTheory.TheContinuedCurrentRetainsTheRoughVariance
import GaloisForLFunctions.EulerFETransportTheory.TheContinuedCurrentReturnsWithItsPrimeHead
import GaloisForLFunctions.EulerFETransportTheory.UnequalCoefficientsFloorTheAbelMass
import GaloisForLFunctions.EulerFETransportTheory.MissingResonancesCostLogarithmicDefectEnergy
import GaloisForLFunctions.EulerFETransportTheory.PolynomialStripContinuationsLieInTheHamburgerClass
import GaloisForLFunctions.EulerFETransportTheory.RealWeightedFakesOnTheIntegers
import GaloisForLFunctions.EulerFETransportTheory.TentPairingsOfDecayingDefects
import GaloisForLFunctions.EulerFETransportTheory.DecayingTentErrorsAreSmall
import GaloisForLFunctions.EulerFETransportTheory.RecurrenceThroughSparseErrors
import GaloisForLFunctions.EulerFETransportTheory.DecayingDefectsVanishInTheUnitGap
import GaloisForLFunctions.EulerFETransportTheory.DecayingDefectsForceIntegerSupport
import GaloisForLFunctions.EulerFETransportTheory.DecayingFunctionalEquationsDetermineThePrimes
import GaloisForLFunctions.EulerFETransportTheory.RieszCountOfAContinuedEulerProduct
import GaloisForLFunctions.EulerFETransportTheory.MobiusInvertedOverRegularPrimes
import GaloisForLFunctions.EulerFETransportTheory.PointMassDiscretizationsOfALaplaceDensity
import GaloisForLFunctions.EulerFETransportTheory.ArbitrarilySlowDefectsOfPositiveWeightedSystems

/-!
# Euler–functional-equation transport

For countable generalized-prime systems in the Hamburger strip class, integrable or
square-integrable uncompleted functional-equation defects force exactly the rational-prime
system. Boundary recurrence supplies this classification;
the two imaginary rays preserve the exact square-integrable defect energy.
Their boundary operator extends uniquely to all square-integrable sources.
An explicit Gamma–Mellin source identifies every finite-energy defect with a half-line
Laplace transform, and the resulting transforms exhaust the right-half-plane Hardy class.
Their vertical traces converge strongly to the canonical boundary, whose normalized
operator is unitary onto the Hardy boundary space.
Every finite-energy theta defect satisfies the actual arithmetic tent identity with
this canonical boundary as its error term.
The errors vanish uniformly with width and at fixed width under large positive translations.
The atomic mass floor therefore imposes the two-width recurrence law, forcing
all sufficiently small unit-gap tents to have zero boundary pairing.
Lebesgue differentiation then forces the real boundary to vanish almost everywhere
in the positive unit gap.
Reflection removes the negative gap too; the origin Fejér identity then forces
every generalized-integer norm to be a natural number.
The half-line Laplace estimate removes every radial defect residue and forces pole reality.
Integer periodicity fixes the pole coefficient and every atomic mass, and excludes
all missing positive integers.
The generalized integers and prime generators are therefore exactly the ordinary ones.
Every nonclassical system in this class has infinite uncompleted defect energy.
Positive continuous prime measures behave differently: adding the exponential pushforward
of `ε x exp(-x) dx` to the Riemann prime-power measure multiplies zeta by
`exp(ε/(s+1)^2)`. This nontrivial positive Euler family satisfies the same Hamburger
strip conditions, preserves every zero on the right half-plane, and admits arbitrarily
small inverse-square majorants for its integrable, square-integrable defect.
The finite-energy defect itself vanishes almost everywhere in the theta formulation
and pointwise in the original Hamburger strip identity.
Local theta data determine every polynomially bounded defect, without a finite-cost
assumption. This also gives pointwise annihilation of the integrable strip defect.
For the literal Gaussian seed, local differential-defect data identify an entire
admissible causal density. Only the scalar identity term is invisible.
Full causal measures are likewise recovered off zero, including infinitely many
atoms and infinite undamped mass. Gaussian-weighted admission is closed under
convolution. A normalized real signed atomic correction can restore the Gaussian
defect after continuous surgery only when both corrections are trivial.
At high ordinates, conductor normalization turns the actual functional equation
into conjugate height reflection with uniformly vanishing absolute error on
every bounded part of the open critical strip.
For every escaping sequence, a connected upper-half-plane domain supporting
locally bounded translates and meeting the Euler half-plane lies strictly right
of the critical line. Whole-quadrant local boundedness is impossible.
Zero-transport equivalences specify the further height-replication target.
The full Gaussian prime current has a continued finite part after subtraction
of its Gamma zero modes. A finite exceptional layer suffices whenever every
complementary zero lies strictly left of the observation line. Reflection of
the full finite part retains exactly the polar and archimedean background.
At every actual zero, the full nonresonant Gamma field is absolutely admitted.
Its subtraction leaves a logarithmic term with the exact divisor multiplicity;
comparison of two positive damping scales cancels the finite-part constant.
At a rightmost zero the nonresonant field is uniformly bounded. The raw
prime-minus-continuum current divided by logarithmic damping scale therefore
recovers its divisor multiplicity. Failure of AAL supplies such an off-line zero.
The archimedean Gaussian current differs from `exp (-y)` times its undamped
value by at most `y * exp (-y) / re s`, uniformly over the whole right half-plane.
This is the unique scalar normalization with bounded error on a positive vertical line.
The complete Gamma-subtracted prime current has error
`O(y * (1 + y) * (1 + log (im s)))` on a positive strip away from the divisor.
Its logarithmically weighted error vanishes uniformly at arbitrary heights;
its absolute error vanishes when damping times logarithmic height tends to zero.
Failure of AAL supplies a whole high strip with these laws, whose left boundary
lies below an actual exceptional abscissa.
With a finite exceptional layer, the entire complementary Gamma field gains
the damping power set by its horizontal gap. Only the finitely many
exceptional modes are needed in the high-strip renormalization.
At inverse-height damping, those finite modes and the continuum also vanish.
The literal infinite von Mangoldt sum recovers the normalized continued
finite part uniformly on an interior high strip supplied by failure of AAL.
The scalar and polar corrections vanish too, leaving the continued Euler
current `-ζ'/ζ` as the limit.
The same passage holds at damping `1/T` uniformly throughout each escaping
window `T ≤ im s ≤ 2T`, matching the arithmetic observation scale.
Under every fixed smooth prime-head probe, the complete Gaussian rough current
retains its exact diagonal mean square as damping vanishes at reciprocal
observation height, on both initial and escaping dyadic windows.
The literal rough von Mangoldt coefficients are admitted for every abscissa
greater than one half; their variance vanishes as the prime cutoff grows.
The small-prime series, including all prime powers, is absolutely admitted
at every positive abscissa and equals the finite Euler logarithmic current.
Under failure of AAL, the continued current after adding back this head
has exactly the same conditioned rough variance on escaping dyadic windows.
One line below an exceptional abscissa serves every fixed head probe and
is zero-free above a finite height.
Geometric prime probes then select any prescribed finite prime phases together
with rough energy below its variance plus any positive slack, in every
sufficiently high dyadic window. This is a scalar current return law;
same-depth zero replication remains open.
-/
