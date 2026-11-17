import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCenteredEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFullPrimeMatrixHasRamanujanSpectralPoints

/-!
# Clipped spectral energy of prime interactions

The literal prime matrix is real symmetric with zero diagonal. Adding the
identity therefore produces a unit-diagonal Hermitian matrix at every real
coupling. Its prime-edge energy survives clipping and arbitrary doubling of
integer labels, without positivity or a spectral-width assumption.
-/

open Matrix
open scoped NNReal
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open HilbertMetric.Clipped ArithmeticIntersectionTheory
noncomputable section

def primeInteraction (N : ℕ) (t : ℝ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℂ :=
  (t : ℂ) • (fullPrimeMatrix N).map Complex.ofReal

theorem primeInteraction_hermitian (N : ℕ) (t : ℝ) :
    (primeInteraction N t).IsHermitian := by
  ext i j
  simp only [primeInteraction, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
  have hs : fullPrimeMatrix N j i = fullPrimeMatrix N i j := by
    simpa using (fullPrimeMatrix_isHermitian N).apply i j
  rw [hs]
  exact mul_comm _ _

theorem primeInteraction_diagonal (N : ℕ) (t : ℝ) (i : PrimeHorizonIndex N) :
    primeInteraction N t i i = 0 := by
  simp [primeInteraction, fullPrimeMatrix, weilPrimeKernel_self_eq]

/-- The spectral square is the literal sum of squared prime interactions. -/
theorem primeInteraction_square (N : ℕ) (t : ℝ) :
    (trace (primeInteraction N t * primeInteraction N t)).re =
      t ^ 2 * ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N, (fullPrimeMatrix N i j) ^ 2 := by
  rw [trace_square (primeInteraction_hermitian N t)]
  simp only [primeInteraction, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two, Finset.mul_sum]

/-- Prime-edge square energy supplies an unconditional clipped defect bound. -/
theorem primeInteraction_clippedDefect (N : ℕ) (t : ℝ) (τ : ℝ≥0) :
    min (t ^ 2 * ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
      (fullPrimeMatrix N i j) ^ 2) ((τ : ℝ) ^ 2) ≤
        defectEnergy τ (1 + primeInteraction N t) := by
  simpa only [primeInteraction_square] using shifted_defect_lower (primeInteraction_hermitian N t) τ

/-- Prime interactions persist through any independently selected double multiplicities. -/
theorem primeInteraction_mixed_clipping (N : ℕ) (t : ℝ)
    (doubled : PrimeHorizonIndex N → Bool) (τ : ℝ≥0) :
    min (t ^ 2 * ∑ i : PrimeHorizonIndex N, ∑ j : PrimeHorizonIndex N,
      (fullPrimeMatrix N i j) ^ 2) ((τ : ℝ) ^ 2) + ∑ i, binaryWeight doubled i ^ 2 ≤
        energy (mixedCutoff τ) (weightedGram (binaryWeight doubled) (1 + primeInteraction N t)) := by
  simpa only [primeInteraction_square] using shifted_mixed_bound
    (primeInteraction_hermitian N t) (primeInteraction_diagonal N t) doubled τ

#print axioms primeInteraction_clippedDefect
#print axioms primeInteraction_mixed_clipping

end
end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
