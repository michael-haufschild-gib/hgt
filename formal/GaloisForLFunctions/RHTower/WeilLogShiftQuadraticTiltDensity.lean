import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticTiltLaw
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuadraticLimit

/-! Normalized quadratic-tilt densities on the common quantile space converge in L1. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilCanonicalQuadraticTiltQuantileDensity (r k : ℕ) (a b d u : ℝ) : ℝ :=
  Real.exp (finiteWeilJointQuadratic a b d (finiteWeilCanonicalJointQuantile r k u)) /
    ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
      ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2)))

def finiteWeilGaussianQuadraticTiltQuantileDensity (a b : ℝ)
    (d : {d : ℝ // a + 2 * b + d < 2}) (u : ℝ) : ℝ :=
  Real.exp (finiteWeilJointQuadratic a b d.val (finiteWeilDiagonalGaussianQuantile u)) /
    Real.sqrt (2 / (2 - (a + 2 * b + d.val)))

theorem finiteWeilQuadraticTilt_normalizer_pos (s : {s : ℝ // s < 2}) :
    0 < Real.sqrt (2 / (2 - s.val)) := by
  have hs : 0 < 2 - s.val := sub_pos.mpr s.property
  positivity

theorem finiteWeilCanonicalQuadraticTiltQuantileDensity_integrable (r k : ℕ) (a b d : ℝ) :
    Integrable (finiteWeilCanonicalQuadraticTiltQuantileDensity r k a b d)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (finiteWeilCanonicalJointQuantile_quadratic_exponential_integrable r k a b d).div_const _

theorem finiteWeilGaussianQuadraticTiltQuantileDensity_integrable (a b : ℝ)
    (d : {d : ℝ // a + 2 * b + d < 2}) :
    Integrable (finiteWeilGaussianQuadraticTiltQuantileDensity a b d)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ((finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integrable_iff a b d.val).mpr
    d.property).div_const _

theorem finiteWeilCanonicalQuadraticTiltQuantileDensity_integral (r k : ℕ) (a b d : ℝ) :
    (∫ u, finiteWeilCanonicalQuadraticTiltQuantileDensity r k a b d u
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) = 1 := by
  unfold finiteWeilCanonicalQuadraticTiltQuantileDensity
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, finiteWeilCanonicalJointQuantile_quadratic_exponential_integral]
  exact mul_inv_cancel₀ (finiteWeilCanonicalJointQuadratic_partition_pos r k a b d).ne'

theorem finiteWeilGaussianQuadraticTiltQuantileDensity_integral (a b : ℝ)
    (d : {d : ℝ // a + 2 * b + d < 2}) :
    (∫ u, finiteWeilGaussianQuadraticTiltQuantileDensity a b d u
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) = 1 := by
  unfold finiteWeilGaussianQuadraticTiltQuantileDensity
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integral]
  exact mul_inv_cancel₀ (finiteWeilQuadraticTilt_normalizer_pos
    ⟨a + 2 * b + d.val, d.property⟩).ne'

theorem ae_tendsto_finiteWeilCanonicalQuadraticTiltQuantileDensity
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) :
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      Tendsto (fun r => finiteWeilCanonicalQuadraticTiltQuantileDensity
        r (2 * (r + 1) ^ 2 + t r) a b d.val u) atTop
          (𝓝 (finiteWeilGaussianQuadraticTiltQuantileDensity a b d u)) := by
  filter_upwards [ae_tendsto_finiteWeilCanonicalJointQuantile_quadratic_exponential t a b d.val]
    with u hu
  exact hu.div (tendsto_finiteWeilCanonicalJoint_quadratic_exponential_subcritical t a b d)
    (finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩).ne'

theorem tendsto_finiteWeilCanonicalQuadraticTiltQuantileDensity_L1
    (t : ℕ → ℕ) (a b : ℝ) (d : {d : ℝ // a + 2 * b + d < 2}) :
    Tendsto (fun r => ∫ u, |finiteWeilCanonicalQuadraticTiltQuantileDensity
      r (2 * (r + 1) ^ 2 + t r) a b d.val u - finiteWeilGaussianQuadraticTiltQuantileDensity a b d u|
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) atTop (𝓝 0) := by
  apply tendsto_integral_abs_sub_of_tendsto
    (fun r => finiteWeilCanonicalQuadraticTiltQuantileDensity_integrable r _ a b d.val)
    (finiteWeilGaussianQuadraticTiltQuantileDensity_integrable a b d)
  · intro r
    exact Eventually.of_forall fun _ => div_nonneg (Real.exp_pos _).le
      (finiteWeilCanonicalJointQuadratic_partition_pos r _ a b d.val).le
  · exact Eventually.of_forall fun _ => div_nonneg (Real.exp_pos _).le
      (finiteWeilQuadraticTilt_normalizer_pos ⟨a + 2 * b + d.val, d.property⟩).le
  · exact ae_tendsto_finiteWeilCanonicalQuadraticTiltQuantileDensity t a b d
  · simp only [finiteWeilCanonicalQuadraticTiltQuantileDensity_integral,
      finiteWeilGaussianQuadraticTiltQuantileDensity_integral]
    exact tendsto_const_nhds

end RHTower
