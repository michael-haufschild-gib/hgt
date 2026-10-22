import Mathlib
import GaloisForLFunctions.RHTower.Schanuel.SchanuelWeldApex
import GaloisForLFunctions.RHTower.BakerProof.BakerIteration
import GaloisForLFunctions.RHTower.GelfondSchneider

/-!
# The weld-spectrum independence ladder

The archimedean–difference weld `𝓜⁺` carries the prime-log rate spectrum `{log p} ⊆ ℝ`.
Its independence hierarchy is now:

* `ℤ`-linear independence (`primeLog_linearIndependent`) — unique factorization;
* `ℚ̄`-linear independence (`bakerLinearIndependence_holds`) — unconditional Baker;
* transcendence of each pairwise ratio (`log_ratio_transcendental`) — unconditional
  Gelfond–Schneider;
* algebraic independence over `ℚ`
  (`schanuelConjecture_iff_and_primeLogs_algebraicallyIndependent`) — the Schanuel apex.

The former Schanuel-to-Baker and Schanuel-to-Gelfond wrappers were useful while the lower rungs
were open interfaces.  They are removed now that both conclusions are native theorems.
-/

namespace GaloisForLFunctions.RHTower

/-- Distinct prime logarithms are linearly independent over the algebraic numbers, unconditionally.
This is the scalar-field form of `bakerLinearIndependence_holds`. -/
theorem primeLogs_algClosure_linearIndependent
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p) :
    LinearIndependent (algebraicClosure ℚ ℂ) (fun i => (Real.log (p i) : ℂ)) :=
  (bakerLinearIndependence_iff_algClosure.mp bakerLinearIndependence_holds)
    n p hpinj hp

end GaloisForLFunctions.RHTower
