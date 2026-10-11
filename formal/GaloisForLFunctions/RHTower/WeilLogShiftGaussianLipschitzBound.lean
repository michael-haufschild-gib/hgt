import GaloisForLFunctions.RHTower.WeilLogShiftGaussianMeanGap
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianTestIntegrability

/-! Uniform integral bounds for unbounded Lipschitz observables and the Gaussian target. -/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalGaussianLipschitz_integral_gap_le_mean
    (r k : ℕ) (a b : ℝ) (L : NNReal) (f : {f : ℝ → ℝ // LipschitzWith L f}) :
    |(∫ x, f.val x ∂(finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)) -
      (∫ x, f.val x ∂(finiteWeilProjectedGaussian a b : Measure ℝ))| ≤
      (L : ℝ) * finiteWeilCanonicalGaussianMeanGap r k a b := by
  have hπ := finiteWeilCanonicalGaussianCoupling_isCoupling r k a b
  have h1 := finiteWeilCanonicalGaussianCoupling_lipschitz_fst_integrable r k a b L f
  have h2 := finiteWeilCanonicalGaussianCoupling_lipschitz_snd_integrable r k a b L f
  have hd : Integrable (fun z : ℝ × ℝ => f.val z.1 - f.val z.2)
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) := h1.sub h2
  rw [← hπ.integral_fst f.property.continuous,
    ← hπ.integral_snd f.property.continuous, ← integral_sub h1 h2]
  calc
    _ ≤ ∫ z, |f.val z.1 - f.val z.2|
        ∂(finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ :=
          (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)))
          (fun z : ℝ × ℝ => f.val z.1 - f.val z.2))
    _ ≤ ∫ z, (L : ℝ) * |z.1 - z.2|
        ∂(finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) := by
      apply integral_mono hd.abs
        ((finiteWeilCanonicalGaussianCoupling_gap_integrable r k a b).const_mul (L : ℝ))
      intro z
      simpa only [Real.dist_eq] using f.property.dist_le_mul z.1 z.2
    _ = _ := integral_const_mul (L : ℝ) _

theorem finiteWeilCanonicalGaussianLipschitz_integral_gap_le_sqrt_cost
    (r k : ℕ) (a b : ℝ) (L : NNReal) (f : {f : ℝ → ℝ // LipschitzWith L f}) :
    |(∫ x, f.val x ∂(finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)) -
      (∫ x, f.val x ∂(finiteWeilProjectedGaussian a b : Measure ℝ))| ≤
      (L : ℝ) * Real.sqrt (finiteWeilCanonicalGaussianQuadraticCost r k a b) :=
  (finiteWeilCanonicalGaussianLipschitz_integral_gap_le_mean r k a b L f).trans
    (mul_le_mul_of_nonneg_left (finiteWeilCanonicalGaussianMeanGap_le_sqrt_cost r k a b)
      (NNReal.coe_nonneg L))

end RHTower
