import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheZerosOfAPrimitiveLFunction
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheExplicitFormulaForACharacter
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterSumsInShortWindows

/-!
# Primes in short intervals of a residue class

Hoheisel's theorem for a fixed modulus: primes `p ≡ a mod q` in every interval `(x, x + x^θ]`
for some `θ < 1`.

* The zeros of a primitive `Λ(s, χ)` lie in the open critical strip, with the Hadamard partial
  fraction of `Λ'/Λ` (`TheZerosOfAPrimitiveLFunction`).
* The genus-kernel explicit formula for `ψ(X, χ)` (`TheExplicitFormulaForACharacter`).
* `ψ(x + h, χ) − ψ(x, χ)` is bounded by window masses of `ψ` and a weighted sum over the zeros
  (`CharacterSumsInShortWindows`).
-/
