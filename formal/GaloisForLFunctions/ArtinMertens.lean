import GaloisForLFunctions.ArtinMertens.TheIdealVonMangoldtIdentity
import GaloisForLFunctions.ArtinMertens.ThePrimeIdealsSatisfyChebyshevBounds
import GaloisForLFunctions.ArtinMertens.TheSoftMertensTheoremForPrimeIdeals
import GaloisForLFunctions.ArtinMertens.TheDegreeOnePrimesCarryTheMertensSum

/-!
# Mertens' theorem for Artin L-functions

Umbrella for the programme proving `Σ_{p ≤ y} φ(Frob_p) log p/p = ⟨φ, 1⟩ log y + O(1)` for a finite
Galois extension `K/ℚ` and a class function `φ` on its Galois group: the ideal von Mangoldt identity
and the hyperbola identity over a number field; the Chebyshev bound for prime ideals; the soft
Mertens theorem `Σ_{N𝔭^k ≤ x} log N𝔭/N𝔭^k ∼ log x`; its degree-one form
`Σ_{p ≤ x} #{𝔭 : N𝔭 = p} log p/p ∼ log x`.
-/
