import GaloisForLFunctions.ArtinMertens.TheIdealVonMangoldtIdentity
import GaloisForLFunctions.ArtinMertens.ThePrimeIdealsSatisfyChebyshevBounds
import GaloisForLFunctions.ArtinMertens.TheSoftMertensTheoremForPrimeIdeals
import GaloisForLFunctions.ArtinMertens.TheDegreeOnePrimesCarryTheMertensSum
import GaloisForLFunctions.ArtinMertens.TheDegreeOnePrimesOfAFixedFieldCountFixedCosets
import GaloisForLFunctions.ArtinMertens.ThePermutationCharactersSatisfyMertens
import GaloisForLFunctions.ArtinMertens.TheFrobeniusDensityTheoremInMertensForm
import GaloisForLFunctions.ArtinMertens.LatticePointsInADomainWithLipschitzBoundary
import GaloisForLFunctions.ArtinMertens.TheFrontierOfTheNormBallIsLipschitz
import GaloisForLFunctions.ArtinMertens.TheIdealCountHasAPowerSavingErrorTerm
import GaloisForLFunctions.ArtinMertens.TheMertensTheoremForPrimeIdealsHasABoundedError
import GaloisForLFunctions.ArtinMertens.PrimePowerWeightsHavePowerBounds
import GaloisForLFunctions.ArtinMertens.TheFrobeniusDensityTheoremWithBoundedError

/-!
# Mertens' theorem for Artin L-functions

Umbrella for the programme proving `Σ_{p ≤ y} φ(Frob_p) log p/p = ⟨φ, 1⟩ log y + O(1)` for a finite
Galois extension `K/ℚ` and a class function `φ` on its Galois group: the ideal von Mangoldt identity
and the hyperbola identity over a number field; the Chebyshev bound for prime ideals; the soft
Mertens theorem `Σ_{N𝔭^k ≤ x} log N𝔭/N𝔭^k ∼ log x`; its degree-one form
`Σ_{p ≤ x} #{𝔭 : N𝔭 = p} log p/p ∼ log x`; the count of degree-one primes of a fixed field `L^H` as
the permutation character `π_H(Frob_p)`; Mertens for permutation characters; Artin induction and
`Σ_{p ≤ x} φ(Frob_p) log p/p ∼ ⟨φ, 1⟩ log x` for every division-constant `φ` (the Frobenius density
theorem in Mertens form); lattice points in dilates of domains with Lipschitz boundary; the
Lipschitz frontier of the norm ball in the fundamental cone; Weber's `I_K(s) = c_K s + O(s^{1−1/n})`;
Mertens with bounded error for prime ideals; and
`Σ_{p ≤ x} φ(Frob_p) log p/p = ⟨φ, 1⟩ log x + O(1)` for every division-constant `φ`.
-/
