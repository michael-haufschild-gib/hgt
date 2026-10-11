import GaloisForLFunctions.RHTower.WeilLogShiftJointGaussianCost
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianTestIntegrability

/-! Unbounded joint Lipschitz tests are integrable and controlled by actual coupling cost. -/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem finiteWeilDiagonalGaussian_lipschitz_integrable (L : NNReal)
    (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Integrable f.val (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))) := by
  have hi := finiteWeilProjectedGaussian_lipschitz_integrable 1 0 (L * 2)
    ⟨f.val ∘ finiteWeilDiagonalPoint, f.property.comp finiteWeilDiagonalPoint_lipschitz⟩
  have h := (integrable_map_measure f.property.continuous.aestronglyMeasurable
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable).mpr hi
  rwa [finiteWeilDiagonalGaussian_eq_map_projected] at h

theorem finiteWeilCanonicalJointGaussianCoupling_lipschitz_fst_integrable
    (r k : ℕ) (L : NNReal) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => f.val z.1)
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  have h : Integrable f.val ((finiteWeilCanonicalJointGaussianCoupling r k :
      Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))).map Prod.fst) := by
    rw [(finiteWeilCanonicalJointGaussianCoupling_isCoupling r k).1]
    exact finiteWeilCanonicalObservableLaw_integrable r k _ f.val
  exact (integrable_map_measure f.property.continuous.aestronglyMeasurable
    measurable_fst.aemeasurable).mp h

theorem finiteWeilCanonicalJointGaussianCoupling_lipschitz_snd_integrable
    (r k : ℕ) (L : NNReal) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => f.val z.2)
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  have h : Integrable f.val ((finiteWeilCanonicalJointGaussianCoupling r k :
      Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))).map Prod.snd) := by
    rw [(finiteWeilCanonicalJointGaussianCoupling_isCoupling r k).2]
    exact finiteWeilDiagonalGaussian_lipschitz_integrable L f
  exact (integrable_map_measure f.property.continuous.aestronglyMeasurable
    measurable_snd.aemeasurable).mp h

theorem finiteWeilCanonicalJointGaussianLipschitz_integral_gap
    (r k : ℕ) (L : NNReal) (f : {f : EuclideanSpace ℝ (Fin 2) → ℝ // LipschitzWith L f}) :
    |(∫ x, f.val x ∂(finiteWeilCanonicalJointProbabilityLaw r k :
          Measure (EuclideanSpace ℝ (Fin 2)))) -
      (∫ x, f.val x ∂(finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))))| ≤
      (L : ℝ) * finiteWeilCanonicalJointGaussianCost r k := by
  have hπ := finiteWeilCanonicalJointGaussianCoupling_isCoupling r k
  have h1 := finiteWeilCanonicalJointGaussianCoupling_lipschitz_fst_integrable r k L f
  have h2 := finiteWeilCanonicalJointGaussianCoupling_lipschitz_snd_integrable r k L f
  have hd : Integrable
      (fun z : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => f.val z.1 - f.val z.2)
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := h1.sub h2
  rw [← hπ.integral_fst f.property.continuous,
    ← hπ.integral_snd f.property.continuous, ← integral_sub h1 h2]
  calc
    _ ≤ ∫ z, |f.val z.1 - f.val z.2| ∂(finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := (finiteWeilCanonicalJointGaussianCoupling r k :
          Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))))
          (fun z => f.val z.1 - f.val z.2))
    _ ≤ ∫ z, (L : ℝ) * dist z.1 z.2 ∂(finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
      apply integral_mono hd.abs
        ((finiteWeilCanonicalJointGaussianCoupling_dist_integrable r k).const_mul (L : ℝ))
      intro z
      simpa only [Real.dist_eq] using f.property.dist_le_mul z.1 z.2
    _ = _ := integral_const_mul (L : ℝ) _

end RHTower
