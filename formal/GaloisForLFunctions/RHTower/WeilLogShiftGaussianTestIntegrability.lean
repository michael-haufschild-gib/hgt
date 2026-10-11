import GaloisForLFunctions.RHTower.WeilLogShiftGaussianCoupling

/-! Every Lipschitz test is integrable under both Gaussian coupling marginals. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem finiteWeilProjectedGaussian_lipschitz_integrable (a b : ℝ) (L : NNReal)
    (f : {f : ℝ → ℝ // LipschitzWith L f}) :
    Integrable f.val (finiteWeilProjectedGaussian a b : Measure ℝ) := by
  have hi : Integrable (fun x : ℝ => x) (finiteWeilProjectedGaussian a b : Measure ℝ) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hbound : Integrable (fun x : ℝ => |f.val 0| + (L : ℝ) * |x|)
      (finiteWeilProjectedGaussian a b : Measure ℝ) :=
    (integrable_const |f.val 0|).add (hi.abs.const_mul (L : ℝ))
  apply hbound.mono' f.property.continuous.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  have h := f.property.dist_le_mul x 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
  calc
    |f.val x| = |(f.val x - f.val 0) + f.val 0| := by rw [sub_add_cancel]
    _ ≤ |f.val x - f.val 0| + |f.val 0| := abs_add_le _ _
    _ ≤ (L : ℝ) * |x| + |f.val 0| := by linarith only [h]
    _ = |f.val 0| + (L : ℝ) * |x| := add_comm _ _

theorem finiteWeilCanonicalGaussianCoupling_lipschitz_fst_integrable
    (r k : ℕ) (a b : ℝ) (L : NNReal) (f : {f : ℝ → ℝ // LipschitzWith L f}) :
    Integrable (fun z : ℝ × ℝ => f.val z.1)
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) := by
  have h : Integrable f.val
      ((finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)).map Prod.fst) := by
    rw [(finiteWeilCanonicalGaussianCoupling_isCoupling r k a b).1]
    exact finiteWeilCanonicalProjectedProbabilityLaw_integrable r k a b f.val
  exact (integrable_map_measure f.property.continuous.aestronglyMeasurable
    measurable_fst.aemeasurable).mp h

theorem finiteWeilCanonicalGaussianCoupling_lipschitz_snd_integrable
    (r k : ℕ) (a b : ℝ) (L : NNReal) (f : {f : ℝ → ℝ // LipschitzWith L f}) :
    Integrable (fun z : ℝ × ℝ => f.val z.2)
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) := by
  have h : Integrable f.val
      ((finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)).map Prod.snd) := by
    rw [(finiteWeilCanonicalGaussianCoupling_isCoupling r k a b).2]
    exact finiteWeilProjectedGaussian_lipschitz_integrable a b L f
  exact (integrable_map_measure f.property.continuous.aestronglyMeasurable
    measurable_snd.aemeasurable).mp h

end RHTower
