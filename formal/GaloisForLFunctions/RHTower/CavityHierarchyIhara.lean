import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
import GaloisForLFunctions.HTGeometry.CavityResponseConvergence
import GaloisForLFunctions.RHTower.IharaBlockSelector
/-!
# Cavity hierarchy in reciprocal Ihara blocks

The generating function in arXiv:2608.14343 is the reciprocal of the existing
Ihara quadratic block. Its finite remainder transfers directly. The normalized
cavity detuning supplies an explicit unconditional family satisfying the Ihara
spectral selector and hence the critical-circle zero law.
-/

open scoped BigOperators
namespace GaloisForLFunctions
noncomputable section
open HTGeometry
/-- Every Ihara block has the same exact finite reciprocal expansion as the cavity response. -/
theorem iharaBlock_cavity_finite_remainder (q lam : ℝ) (z : ℂ) (n : ℕ) :
    iharaBlock q lam z *
        (∑ k ∈ Finset.range (n + 1), quadraticResponseCoeff (-(lam : ℂ)) (q : ℂ) k * z ^ k) =
      1 - quadraticResponseCoeff (-(lam : ℂ)) (q : ℂ) (n + 1) * z ^ (n + 1) +
        (q : ℂ) * quadraticResponseCoeff (-(lam : ℂ)) (q : ℂ) n * z ^ (n + 2) := by
  simpa only [iharaBlock, neg_mul, ← sub_eq_add_neg] using
    quadraticResponseCoeff_finite_remainder (-(lam : ℂ)) (q : ℂ) z n
/-- Cavity-normalized detuning supplies a closed family of Ihara spectral selectors. -/
theorem cavityCoordinate_ihara_spectral_bound (D E r : ℝ) :
    blockSpectralBound (r ^ 2) (2 * r * cavityChebyshevCoordinate D E) := by
  have hx := abs_cavityChebyshevCoordinate_le_one D E
  have hx2 : cavityChebyshevCoordinate D E ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hx
  unfold blockSpectralBound
  nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hx2)]
/-- A strictly positive parameterized Ihara family has all zeros on its critical circle. -/
theorem cavityCoordinate_ihara_zerosOnCriticalCircle (D E r : ℝ) :
    zerosOnCriticalCircle ((r ^ 2 + 1) ^ 2)
      (2 * (r ^ 2 + 1) * cavityChebyshevCoordinate D E) := by
  exact zerosOnCriticalCircle_of_spectral_bound (by positivity)
    (cavityCoordinate_ihara_spectral_bound D E (r ^ 2 + 1))
end
end GaloisForLFunctions
