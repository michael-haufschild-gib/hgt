import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheZerosOfAPrimitiveLFunction
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheExplicitFormulaForACharacter
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterSumsInShortWindows
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LocalZeroCount
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterPhaseBlocks
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LittlewoodGrowth
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LittlewoodZeroFreeRegion
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.ZeroDetectionForACharacter
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.ZeroDensityForACharacter
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.TheZeroSumVanishes
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.CharacterWindows
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.PrimesInShortProgressions
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.UniformZeroCounts
import GaloisForLFunctions.ShortIntervalPrimesInProgressions.SiegelWalfisz

/-!
# Primes in short intervals of a residue class

Hoheisel's theorem for a fixed modulus: for `θ = 1 − 1/(16(14·10⁷ + 12))`, every interval
`(x, x + x^θ]` with `x` large contains a prime `p ≡ a (mod q)`, and the von Mangoldt mass of the
class in the interval is `∼ x^θ/φ(q)` (`PrimesInShortProgressions`).

* Zeros of a primitive `Λ(s, χ)` and the Hadamard partial fraction (`TheZerosOfAPrimitiveLFunction`);
  the explicit formula (`TheExplicitFormulaForACharacter`); the window bound by a weighted zero sum
  (`CharacterSumsInShortWindows`); the local zero count (`LocalZeroCount`).
* Littlewood's growth bound for `L(s, χ)` from the `k`-th derivative test on additive twists
  (`CharacterPhaseBlocks`, `LittlewoodGrowth`), and Littlewood's zero-free region
  (`LittlewoodZeroFreeRegion`).
* The zero-density estimate `N(σ, T) ≪ (log T)^{11} T^{12(1−σ)}` by mollified detection and the
  discrete mean value theorem (`ZeroDetectionForACharacter`, `ZeroDensityForACharacter`).
* The weighted zero sum vanishes (`TheZeroSumVanishes`); windows of `ψ(·, χ)` for every character
  (`CharacterWindows`).
* Uniformly in the modulus: zero counts through the functional-equation reflection
  (`UniformZeroCounts`), and the Siegel–Walfisz theorem in short windows,
  `|ψ(x+h, χ) − ψ(x, χ)| ≤ h/(log x)^A` for primitive `χ` of modulus `≤ (log x)^B` and
  `h ≥ x/(log x)^H` (`SiegelWalfisz`).
-/
