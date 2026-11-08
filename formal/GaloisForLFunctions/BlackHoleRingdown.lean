import GaloisForLFunctions.BlackHoleRingdown.NoNearArithmeticLadderOfZeros
import GaloisForLFunctions.BlackHoleRingdown.RingdownReadsTheHorizonSpectrum
import GaloisForLFunctions.BlackHoleRingdown.TheEchoTrainOfTheCusp
import GaloisForLFunctions.BlackHoleRingdown.TheCausalSymbolOfTheModularHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheSharpAnalyticBoundary
import GaloisForLFunctions.BlackHoleRingdown.TheProbesPreserveEveryResonance
import GaloisForLFunctions.BlackHoleRingdown.TheEchoSpikesAndTheirGaussianObservation
import GaloisForLFunctions.BlackHoleRingdown.TheGaussianObservationOfTheEchoSource
import GaloisForLFunctions.BlackHoleRingdown.TheExactLiftOfTheModularWave
import GaloisForLFunctions.BlackHoleRingdown.TheVerticalBoundsOfTheEisensteinTail
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour
import GaloisForLFunctions.BlackHoleRingdown.TheNormalizedEisensteinFunction
import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinWavePacket
import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfTheModularHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheFieldIsSmoothAcrossTheHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownExpansion
import GaloisForLFunctions.BlackHoleRingdown.TheExpansionIsUniformAtLateTimes
import GaloisForLFunctions.BlackHoleRingdown.TheModesOfTheRingdown
import GaloisForLFunctions.BlackHoleRingdown.TheConvolutionOfThePulseWithTheEchoes
import GaloisForLFunctions.BlackHoleRingdown.TheReflectedSignalIsTheEchoTrain
import GaloisForLFunctions.BlackHoleRingdown.TheFieldCarriesTheCausalSymbol
import GaloisForLFunctions.BlackHoleRingdown.TheSharpDecayOfTheBesselKernel
import GaloisForLFunctions.BlackHoleRingdown.TheSharpBoundsOfTheEisensteinFunction
import GaloisForLFunctions.BlackHoleRingdown.ThePolynomialGrowthOfTheEisensteinFunction
import GaloisForLFunctions.BlackHoleRingdown.TheLiftOfAnyModularWave
import GaloisForLFunctions.BlackHoleRingdown.TheImageFieldOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.ThePulseAmplitude
import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinFunctionOnContours
import GaloisForLFunctions.BlackHoleRingdown.TheSpectrumOfTheImageField
import GaloisForLFunctions.BlackHoleRingdown.TheContourPackage
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheEchoesOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheVolumeOfTheModularHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinChannel
import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsVanishAtTheCusp
import GaloisForLFunctions.BlackHoleRingdown.TheCuspChannel
import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsExist
import GaloisForLFunctions.BlackHoleRingdown.TheCuspSpectrumIsDiscrete
import GaloisForLFunctions.BlackHoleRingdown.TheOddSectorIsACavity
import GaloisForLFunctions.BlackHoleRingdown.TheWeylKernel
import GaloisForLFunctions.BlackHoleRingdown.TheWeylLowerBound
import GaloisForLFunctions.BlackHoleRingdown.TheRingdownRateIsTheZeroFreeStrip
import GaloisForLFunctions.BlackHoleRingdown.TheTwoRatesOfTheHorizonAreOneExponent
import GaloisForLFunctions.BlackHoleRingdown.TheCuspFormsAreGravitationalModes
import GaloisForLFunctions.BlackHoleRingdown.TheHeckeEigenformsOfTheCuspChannel
import GaloisForLFunctions.BlackHoleRingdown.TheHeckeRigidityOfTheCuspModes
import GaloisForLFunctions.BlackHoleRingdown.TheMultiplicityOfTheHeckeModes
import GaloisForLFunctions.BlackHoleRingdown.TheParityOfTheHeckeModes
import GaloisForLFunctions.BlackHoleRingdown.TheCosineFamilyOfTheHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheGeneralHorizonData
import GaloisForLFunctions.BlackHoleRingdown.TheVectorModesOfTheMetric
import GaloisForLFunctions.BlackHoleRingdown.TheGravitationalModesOfTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheLinearityOfTheEinsteinOperator
import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfARow
import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheMetricRingdown
import GaloisForLFunctions.BlackHoleRingdown.TheScalarWaveOfAPulse
import GaloisForLFunctions.BlackHoleRingdown.TheWaveOnTheQuotient
import GaloisForLFunctions.BlackHoleRingdown.TheModularBlackHoleIsAQuotientOfAntiDeSitter
import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfAPulseIsRegularAcrossTheHorizon
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleReadsTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheAlgebraOfCuspSupportedProfiles
import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleRateIsTheZeroFreeRegion
import GaloisForLFunctions.BlackHoleRingdown.TheLaxPhillipsSemigroupOfTheModularSurface

/-!
# Black-hole ringdown and the zeros of zeta

Ringdown frequencies on exact `sech²` black holes read the spectrum of the horizon. A round horizon
gives a ladder that is an `ℓ²` perturbation of an arithmetic progression, and no such ladder consists of
zeta zeros. A modular horizon carries every zero as a pole of a causal scattering symbol, the retarded
transform of an echo train with delays `2 log c`.

RH is equivalent to analyticity above the sharp quarter-line damping boundary. Functional-equation
partners have a fixed sum of damping rates. The raw echo train has unbounded arrival spikes;
Gaussian observation integrals converge absolutely, retain the exact source transform, and preserve every
arithmetic pole with its multiplicity.

On the massless topological AdS black hole with horizon `PSL₂(ℤ)\ℍ`, an Eisenstein wave packet lifts to
exact solutions of the conformally coupled wave equation of the metric, smooth across the future horizon.
Their expansion in damped modes has one mode per zero, on the minus branch only, with a remainder that
decays faster than every exponential, uniformly at late times. The reflected signal is the pulse convolved
with the echo train minus its mean growth, and the causal symbol is the transfer function of the field.

Every compact pulse gives an exact solution by the method of images, with the same echo identity and ringdown. Every
square-integrable function on the horizon is a constant plus a limit of such fields plus a cusp form, and the wave evolution
is a contractive cosine family on the complement of the constants. Cusp forms have `λ ≥ ¼` and undamped horizon modes, at the
universal rate of the boundary condition; the mirror-odd sector is cuspidal, so they exist; their eigenvalues form a discrete unbounded sequence. The whole mirror-odd half of the horizon is cuspidal: the zeros couple only to mirror-even data. Their number below `Λ` is at least a multiple of `Λ` (a Weyl lower bound). The scalar wave of a pulse carries an exact vacuum perturbation of the metric, in the
vector and in the scalar sector, in closed form and covariant under `SL₂(ℤ)`; each zero is a gravitational quasinormal mode, and
each component of the metric rings down in these modes.

The late-time decay exponent of the field of every pulse is half the width of the zero-free strip, at every strength, and the
thermalization exponent of long horocycles is `½` plus the same number: the two RH rates `e^{-τ/4}` and `y^{3/4}` are one exponent.

Every cusp form is smooth and is a gravitational quasinormal mode, in both vector branches and the scalar sector, at exactly
the base damping of its sector; the zeta modes lie strictly deeper, exactly `¼` deeper iff RH, and form a set of density zero.

Each cusp space is finite-dimensional and carries the commuting Hecke operators `T_p`; every eigenvalue of the cusp spectrum
has a Hecke–Maass form, with the trivial bound `|λ_p| ≤ √p + 1/√p` on its normalized Hecke eigenvalues. A Hecke eigenform is determined by its
eigenvalues and its first Fourier modes `a_{±1}`, and each mode lies in a line, so every joint eigenspace of the Laplacian and
the Hecke operators has dimension at most two. The mirror commutes with all of them, and each joint eigenspace of definite
parity is a line, nonzero at every eigenvalue of the cusp spectrum (strong multiplicity one).
-/
