import GaloisForLFunctions.RHTower.SteinhausFiniteNodeCovariance
import GaloisForLFunctions.HilbertMetric.Correlation.ExceptionalEnergy

/-!
# Stability of finite arithmetic covariance

The prime--cofactor feature realization turns the exact Steinhaus covariance
into a Euclidean norm. Removing any coefficient direction obeys the sharp
centered deletion law, including all correlations between coefficient systems.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric
open RHTower
noncomputable section

/-- The concrete vector representing an arithmetic covariance Rayleigh direction. -/
def arithmeticCovarianceVector {J : ℕ} (P : Finset ℕ)
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) :
    EuclideanSpace ℂ (steinhausFiniteNodeFeatureIndex P X) :=
  WithLp.toLp 2 fun q => ∑ j, u j * steinhausFiniteNodeFeature P a X j q

private theorem arithmeticCovarianceVector_norm_sq {J : ℕ} (P : Finset ℕ)
    (a : Fin J → ℕ → ℂ) (u : Fin J → ℂ) (X : ℕ) :
    ‖arithmeticCovarianceVector P a u X‖ ^ 2 =
      steinhausFiniteNodeArithmeticGramEnergy P a u X := by
  rw [PiLp.norm_sq_eq_of_L2, steinhausFiniteNodeArithmeticGramEnergy_eq_feature_sum]
  rfl

private theorem arithmeticCovarianceVector_sub {J : ℕ} (P : Finset ℕ)
    (a : Fin J → ℕ → ℂ) (u v : Fin J → ℂ) (X : ℕ) :
    arithmeticCovarianceVector P a (u - v) X =
      arithmeticCovarianceVector P a u X - arithmeticCovarianceVector P a v X := by
  ext q
  simp [arithmeticCovarianceVector, sub_mul, Finset.sum_sub_distrib]

/-- Exact arithmetic covariance remains stable under arbitrary removed coefficient directions. -/
theorem arithmeticCovariance_deletion_centered {J : ℕ} (P : Finset ℕ)
    (a : Fin J → ℕ → ℂ) (u v : Fin J → ℂ) (X : ℕ) :
    (steinhausFiniteNodeArithmeticGramEnergy P a (u - v) X -
      steinhausFiniteNodeArithmeticGramEnergy P a u X -
      steinhausFiniteNodeArithmeticGramEnergy P a v X) ^ 2 ≤
      4 * steinhausFiniteNodeArithmeticGramEnergy P a u X *
        steinhausFiniteNodeArithmeticGramEnergy P a v X := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (steinhausFiniteNodeFeatureIndex P X)) :=
    InnerProductSpace.rclikeToReal ℂ _
  have h := energy_sub_centered (arithmeticCovarianceVector P a u X)
    (arithmeticCovarianceVector P a v X)
  simpa only [← arithmeticCovarianceVector_sub, arithmeticCovarianceVector_norm_sq] using h

/-- The covariance lost by removing a direction is paid by its full arithmetic Gram energy. -/
theorem arithmeticCovariance_deletion_error {J : ℕ} (P : Finset ℕ)
    (a : Fin J → ℕ → ℂ) (u v : Fin J → ℂ) (X : ℕ) :
    |steinhausFiniteNodeArithmeticGramEnergy P a (u - v) X -
      steinhausFiniteNodeArithmeticGramEnergy P a u X| ≤
      steinhausFiniteNodeArithmeticGramEnergy P a v X +
        2 * Real.sqrt (steinhausFiniteNodeArithmeticGramEnergy P a u X) *
          Real.sqrt (steinhausFiniteNodeArithmeticGramEnergy P a v X) := by
  letI : InnerProductSpace ℝ (EuclideanSpace ℂ (steinhausFiniteNodeFeatureIndex P X)) :=
    InnerProductSpace.rclikeToReal ℂ _
  have h := energy_sub_error (arithmeticCovarianceVector P a u X)
    (arithmeticCovarianceVector P a v X)
  have hn (w : Fin J → ℂ) : Real.sqrt (steinhausFiniteNodeArithmeticGramEnergy P a w X) =
      ‖arithmeticCovarianceVector P a w X‖ := by
    rw [← arithmeticCovarianceVector_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa only [← arithmeticCovarianceVector_sub, arithmeticCovarianceVector_norm_sq, hn] using h

end
end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.arithmeticCovariance_deletion_centered
#print axioms GaloisForLFunctions.HilbertMetric.arithmeticCovariance_deletion_error
