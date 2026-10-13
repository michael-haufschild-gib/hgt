import GaloisForLFunctions.HTGeometry.PowerCovarianceMatrix

/-! Almost-everywhere constant power sums give covariance null vectors and singular determinants. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

theorem powerCovarianceMatrix_mulVec_eq_zero_of_ae_const
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hf : ∀ i : Fin n, MemLp (fun y => f y ^ ((i : ℕ) + 1)) 2 μ)
    (b : ℝ) (hconst : ∀ᵐ y ∂μ, (∑ j : Fin n, c j * f y ^ ((j : ℕ) + 1)) = b) :
    (powerCovarianceMatrix μ f n).mulVec c = 0 := by
  let F : Ω → ℝ := fun y => ∑ j : Fin n, c j * f y ^ ((j : ℕ) + 1)
  have hmean : (∫ y, F y ∂μ) = b := by
    rw [integral_congr_ae hconst]
    simp
  funext i
  have hcov : covariance (fun y => f y ^ ((i : ℕ) + 1)) F μ = 0 := by
    unfold covariance
    rw [hmean]
    apply integral_eq_zero_of_ae
    filter_upwards [hconst] with y hy
    simp [F, hy]
  have hsum := covariance_fun_sum_right (fun j => (hf j).const_mul (c j)) (hf i)
  have htotal := hsum.symm.trans hcov
  change (∑ j : Fin n, covariance (fun y => f y ^ ((i : ℕ) + 1))
    (fun y => f y ^ ((j : ℕ) + 1)) μ * c j) = 0
  simpa only [covariance_const_mul_right, mul_comm] using htotal

theorem powerCovarianceMatrix_det_eq_zero_of_ae_const
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (n : ℕ) (c : Fin n → ℝ)
    (hf : ∀ i : Fin n, MemLp (fun y => f y ^ ((i : ℕ) + 1)) 2 μ)
    (b : ℝ) (hc : c ≠ 0)
    (hconst : ∀ᵐ y ∂μ, (∑ j : Fin n, c j * f y ^ ((j : ℕ) + 1)) = b) :
    (powerCovarianceMatrix μ f n).det = 0 := by
  have hnull := powerCovarianceMatrix_mulVec_eq_zero_of_ae_const μ f n c hf b hconst
  by_contra hdet
  have hunit : IsUnit (powerCovarianceMatrix μ f n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  exact hc ((Matrix.mulVec_injective_of_isUnit hunit)
    (hnull.trans (Matrix.mulVec_zero _).symm))

end GaloisForLFunctions.HTGeometry
