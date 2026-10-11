import GaloisForLFunctions.RHTower.WeilLogShiftJointGaussianQuadratic

/-! Common-L Lipschitz observables admit uniform mean-square comparison under the joint coupling. -/

open MeasureTheory Filter Topology

noncomputable section
namespace RHTower

theorem finiteWeilJointLipschitz_sq_diff_bound (L : NNReal)
    (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f})
    (x y : EuclideanSpace ℝ (Fin 2)) :
    |f.val x - f.val y| ^ 2 ≤ (L : ℝ) ^ 2 * dist x y ^ 2 := by
  have h : |f.val x - f.val y| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq] using f.property.dist_le_mul x y
  have hs := mul_self_le_mul_self (abs_nonneg (f.val x - f.val y)) h
  nlinarith only [hs]

theorem finiteWeilCanonicalJointGaussianCoupling_lipschitz_sq_diff_integrable
    (r k : ℕ) (L : NNReal) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Integrable
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => |f.val z.1 - f.val z.2| ^ 2)
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  have hc : Continuous
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => |f.val z.1 - f.val z.2| ^ 2) :=
    (((f.property.continuous.comp continuous_fst).sub
      (f.property.continuous.comp continuous_snd)).abs).pow 2
  apply ((finiteWeilCanonicalJointGaussianCoupling_quadratic_integrable r k).const_mul
    ((L : ℝ) ^ 2)).mono' hc.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact finiteWeilJointLipschitz_sq_diff_bound L f z.1 z.2

def finiteWeilCanonicalJointGaussianLipschitzQuadraticGap (r k : ℕ) (L : NNReal)
    (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) : ℝ :=
  ∫ z, |f.val z.1 - f.val z.2| ^ 2 ∂(finiteWeilCanonicalJointGaussianCoupling r k :
    Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))

theorem finiteWeilCanonicalJointGaussianLipschitzQuadraticGap_nonneg
    (r k : ℕ) (L : NNReal) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    0 ≤ finiteWeilCanonicalJointGaussianLipschitzQuadraticGap r k L f :=
  integral_nonneg fun z => sq_nonneg |f.val z.1 - f.val z.2|

theorem finiteWeilCanonicalJointGaussianLipschitzQuadraticGap_bound
    (r k : ℕ) (L : NNReal) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    finiteWeilCanonicalJointGaussianLipschitzQuadraticGap r k L f ≤
      (L : ℝ) ^ 2 * finiteWeilCanonicalJointGaussianQuadraticCost r k := by
  calc
    _ ≤ ∫ z, (L : ℝ) ^ 2 * dist z.1 z.2 ^ 2 ∂(finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) :=
      integral_mono (finiteWeilCanonicalJointGaussianCoupling_lipschitz_sq_diff_integrable r k L f)
        ((finiteWeilCanonicalJointGaussianCoupling_quadratic_integrable r k).const_mul ((L : ℝ) ^ 2))
        (fun z => finiteWeilJointLipschitz_sq_diff_bound L f z.1 z.2)
    _ = _ := integral_const_mul ((L : ℝ) ^ 2) _

theorem tendsto_finiteWeilCanonicalJointGaussianLipschitzQuadraticGap_zero
    (t : ℕ → ℕ) (L : NNReal)
    (f : ℕ → {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Tendsto (fun r => finiteWeilCanonicalJointGaussianLipschitzQuadraticGap r
      (2 * (r + 1) ^ 2 + t r) L (f r)) atTop (𝓝 0) := by
  apply squeeze_zero (fun r => finiteWeilCanonicalJointGaussianLipschitzQuadraticGap_nonneg r _ L (f r))
    (fun r => finiteWeilCanonicalJointGaussianLipschitzQuadraticGap_bound r _ L (f r))
  simpa only [mul_zero] using
    (tendsto_finiteWeilCanonicalJointGaussianQuadraticCost_zero t).const_mul ((L : ℝ) ^ 2)

end RHTower
