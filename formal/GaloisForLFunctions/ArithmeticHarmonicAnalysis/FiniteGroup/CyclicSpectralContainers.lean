import GaloisForLFunctions.HTGeometry.FiniteCyclicPairFourier
import GaloisForLFunctions.RHTower.OffLineAnnihilatingWeightsCountCriticalZeros

/-!
# Spectral containers on cyclic groups and residue tori

Support Cauchy–Schwarz and exact Parseval bound concentration in physical space by
Fourier energy. Separating the trivial character gives the centered container bound.
The statements retain the total mass explicitly, so they apply to arbitrary complex
weights without a normalization or positivity premise.
-/

open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

open GaloisForLFunctions.HTGeometry

variable (N : ℕ) [NeZero N]

/-- Cyclic spectral energy controls support concentration, with exact cardinality factor. -/
theorem cyclic_spectral_container (f : ZMod N → ℂ) :
    (N : ℝ) * Complex.normSq (∑ j, f j) ≤
      ((univ.filter fun j => f j ≠ 0).card : ℝ) *
        ∑ k, Complex.normSq (ZMod.dft f k) := by
  have h := _root_.RHTower.ZeroValueConfig.norm_sum_sq_le_card_support_mul univ f
  simp only [← Complex.normSq_eq_norm_sq] at h
  rw [GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval]
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [mul_left_comm] using hm

/-- Removing the trivial frequency isolates the spectral excess above the total mass. -/
theorem cyclic_centered_spectral_container (f : ZMod N → ℂ) :
    (N : ℝ) * Complex.normSq (∑ j, f j) ≤
      ((univ.filter fun j => f j ≠ 0).card : ℝ) *
        (Complex.normSq (∑ j, f j) +
          ∑ k ∈ univ.erase 0, Complex.normSq (ZMod.dft f k)) := by
  have hsum := sum_erase_add (s := (univ : Finset (ZMod N)))
    (fun k => Complex.normSq (ZMod.dft f k)) (mem_univ 0)
  rw [ZMod.dft_apply_zero] at hsum
  rw [← add_comm (∑ k ∈ univ.erase 0, Complex.normSq (ZMod.dft f k)), hsum]
  exact cyclic_spectral_container N f

/-- The same container inequality on the two-coordinate residue torus has volume `N²`. -/
theorem cyclic_pair_spectral_container (f : ZMod N × ZMod N → ℂ) :
    (N : ℝ) ^ 2 * Complex.normSq (∑ j, f j) ≤
      ((univ.filter fun j => f j ≠ 0).card : ℝ) *
        ∑ k, Complex.normSq (cyclicPairFourier f k) := by
  have h := _root_.RHTower.ZeroValueConfig.norm_sum_sq_le_card_support_mul univ f
  simp only [← Complex.normSq_eq_norm_sq] at h
  rw [cyclicPairFourier_parseval]
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg (N : ℝ))
  simpa only [mul_left_comm] using hm

/-- Separating the trivial character gives the centered spectral bound on residue tori. -/
theorem cyclic_pair_centered_spectral_container (f : ZMod N × ZMod N → ℂ) :
    (N : ℝ) ^ 2 * Complex.normSq (∑ j, f j) ≤
      ((univ.filter fun j => f j ≠ 0).card : ℝ) *
        (Complex.normSq (∑ j, f j) +
          ∑ k ∈ univ.erase (0, 0), Complex.normSq (cyclicPairFourier f k)) := by
  have hsum := sum_erase_add (s := (univ : Finset (ZMod N × ZMod N)))
    (fun k => Complex.normSq (cyclicPairFourier f k)) (mem_univ (0, 0))
  rw [cyclicPairFourier_zero] at hsum
  rw [← add_comm (∑ k ∈ univ.erase (0, 0), Complex.normSq (cyclicPairFourier f k)), hsum]
  exact cyclic_pair_spectral_container N f

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.cyclic_spectral_container
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.cyclic_centered_spectral_container
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.cyclic_pair_spectral_container
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.cyclic_pair_centered_spectral_container
