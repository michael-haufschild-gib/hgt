import GaloisForLFunctions.SignFreePurityMechanisms.SimultaneousInseparabilityCostsThePrimorial
import GaloisForLFunctions.SignFreePurityMechanisms.ThePointCountOfSpecZIsLogarithmic
import GaloisForLFunctions.SignFreePurityMechanisms.ThePowerMapIsAFrobeniusAtOnePrime
import GaloisForLFunctions.SignFreePurityMechanisms.TheFermatQuotientIsTheDerivativeAtAPrime
import GaloisForLFunctions.SignFreePurityMechanisms.SeparationForcesRationality
import GaloisForLFunctions.SignFreePurityMechanisms.CoefficientGapsSeparateTheRoots
import GaloisForLFunctions.SignFreePurityMechanisms.TheHeightSeparatesTheZerosIffThePrimeTracesAreBounded
import GaloisForLFunctions.SignFreePurityMechanisms.TheZerosOfZetaHaveNoCoefficientGaps
import GaloisForLFunctions.SignFreePurityMechanisms.TheUltrametricNewtonPolygonSeparatesTheRoots
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitContents
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentRounding
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentPartitions
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.ContentBounds
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitAllocations
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitValues
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitCompositions
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopDigits
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitExchanges
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.IncreasingAllocations
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.InitialCompositions
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.LastBlockOperations
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopBlockFeasibility
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GreedyWeightBounds
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixBoundary

/-!
# Sign-free purity mechanisms

Two proofs of a Riemann hypothesis use no positivity: Stepanov's, through the Frobenius
endomorphism with zero derivative, and the Newton-polygon proof for the Carlitz–Goss zeta
function, through an invariant that separates the roots. This programme determines what `ℤ`
carries of each.

**The Frobenius.**
* The point count `Λ(n) + 1 + 1/(n² − 1)` of `Spec ℤ` is not a cardinality; its prime part is
  `log Φ_n(1)` (`ThePointCountOfSpecZIsLogarithmic`).
* The power map `x ↦ x ^ n` is a Frobenius at exactly one prime when `n` is a prime power and at
  none otherwise; counting these primes with weight `log q` gives `Λ(n)`
  (`ThePowerMapIsAFrobeniusAtOnePrime`).
* On `ℤ` the Fermat quotient is the derivative at `p`: its order is the `p`-adic order, its
  constants are `0, ±1`, and order `m` at the primes of `S` costs exactly `m ∑ log p`
  (`TheFermatQuotientIsTheDerivativeAtAPrime`).
* On `ℤ[X]` Stepanov's identity holds modulo `n` at every order, no endomorphism has zero
  derivative, and inseparability at every prime of `S` costs a degree divisible by the primorial
  of `S` (`SimultaneousInseparabilityCostsThePrimorial`).

**Separation.**
* A Galois-invariant function injective on the roots forces them into the base field
  (`SeparationForcesRationality`).
* Over a complete ultrametric field the coefficients produce the separation: strictly
  log-concave coefficient norms give roots of pairwise distinct norm, and the polynomial splits
  over the base field (`TheUltrametricNewtonPolygonSeparatesTheRoots`).
* Over `ℂ` coefficient gaps of factor `9` produce it, at the price of lacunary roots
  (`CoefficientGapsSeparateTheRoots`); the critical zeros of `ζ` are too dense for these gaps
  (`TheZerosOfZetaHaveNoCoefficientGaps`).
* For `ζ` the separating invariant is the height: it is injective on the zeros exactly when the
  absolute cubic-spline traces at the primes are bounded, and the spread of its fibres is their
  growth exponent (`TheHeightSeparatesTheZerosIffThePrimeTracesAreBounded`).
-/
