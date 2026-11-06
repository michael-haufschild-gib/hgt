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
-/
