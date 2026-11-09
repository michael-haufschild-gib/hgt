import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReturnFormDuality
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.LinearFormsWithExplicitDependenceOnTheirNumber
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheDepthLawOfReturns
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.SurvivalAtADeepReturn
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheReciprocityOfReturns

/-!
# Transcendence theory of the prime orbit

The prime orbit `t ↦ (p^{−it})_p` as a Diophantine object. A return has a depth (its precision at a
fixed set of primes) and a breadth (the number of primes returning together at a fixed precision).
Linear forms in logarithms control depth: explicit Baker bounds give a polynomial depth law,
uniform over the subsets of the primes `≤ y`. At constant precision only forms of bounded height act,
Liouville is sharp for them, and the rounded system shows that no bounded-height Diophantine data
excludes a return past the Kronecker scale. Integrality turns approximate vanishing at a return into
exact vanishing at order `0` at constant precision, at order `1` below the Baker threshold, at
order `2` only qualitatively. The explicit formula is the reciprocity of returns: a return at
height `t` is a configuration of zeros near `t` imitating the pole. See
`TranscendenceTheoryOfThePrimeOrbit/README.md`.
-/
