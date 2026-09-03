import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSplit
import GaloisForLFunctions.RHTower.Sieve.SupportKernelLargeValues

/-!
# Reflection symmetry of harmonic prime blocks

The harmonic prime coefficients are real.  Complex conjugation therefore reverses Gallagher
frequency exactly, so every large-value estimate on one frequency half has an identical reflected
copy on the other half.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Conjugation reverses frequency in the harmonic Möbius phase. -/
theorem conj_harmonicMoebiusPhase (w : ℝ) (n : ℕ) :
    (starRingEnd ℂ) (harmonicMoebiusPhase w n) = harmonicMoebiusPhase (-w) n := by
  rw [harmonicMoebiusPhase, harmonicMoebiusPhase, moebiusPhase, moebiusPhase]
  simp only [map_div₀, map_mul, map_intCast, map_natCast, conj_unitLogPhase]

/-- A harmonic prime block at reflected frequency is the complex conjugate block. -/
theorem conj_harmonicPrimeBlockPoly (B : Finset ℕ) (w : ℝ) :
    (starRingEnd ℂ) (harmonicPrimeBlockPoly B w) = harmonicPrimeBlockPoly B (-w) := by
  simp only [harmonicPrimeBlockPoly, map_sum, conj_harmonicMoebiusPhase]

/-- The norm of a harmonic prime block is even in frequency. -/
theorem norm_harmonicPrimeBlockPoly_neg (B : Finset ℕ) (w : ℝ) :
    ‖harmonicPrimeBlockPoly B (-w)‖ = ‖harmonicPrimeBlockPoly B w‖ := by
  rw [← conj_harmonicPrimeBlockPoly, Complex.norm_conj]

end


end RHTower.Sieve
