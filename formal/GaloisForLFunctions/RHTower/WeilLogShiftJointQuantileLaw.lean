import GaloisForLFunctions.RHTower.WeilLogShiftObservableQuantileAtoms
import GaloisForLFunctions.RHTower.WeilLogShiftJointGaussianCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianQuantile

/-! Joint and Gaussian laws share one explicit uniform-space quantile realization. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry Set

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalProjectedIndex_quantile_eq_atom (r k : ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) :
    ∃ i, quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) p.val =
      finiteWeilCanonicalFluctuationPoint r k i 0 := by
  have h := finiteWeilCanonicalObservableLaw_quantile_eq_atom r k
    (fun i => finiteWeilCanonicalFluctuationPoint r k i 0) p
  have hfun : (fun i : Fin (r + 1) => finiteWeilCanonicalFluctuationPoint r k i 0) =
      (fun i : Fin (r + 1) => (((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k) /
        Real.sqrt ((r + 1 : ℕ) : ℝ)) := by
    funext i
    rfl
  rw [hfun] at h
  simpa only [finiteWeilCanonicalProjectedProbabilityLaw, one_mul, zero_mul, add_zero] using h

def finiteWeilCanonicalJointQuantile (r k : ℕ) (p : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  finiteWeilCanonicalJointLift r k
    (quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) p)

def finiteWeilDiagonalGaussianQuantile (p : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  finiteWeilDiagonalPoint (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) p)

theorem finiteWeilCanonicalJointQuantile_measurable (r k : ℕ) :
    Measurable (finiteWeilCanonicalJointQuantile r k) :=
  (finiteWeilCanonicalJointLift_measurable r k).comp (measurable_quantile _)

theorem finiteWeilDiagonalGaussianQuantile_measurable :
    Measurable finiteWeilDiagonalGaussianQuantile :=
  continuous_finiteWeilDiagonalPoint.measurable.comp (measurable_quantile _)

theorem finiteWeilCanonicalJointQuantile_law (r k : ℕ) :
    Measure.map (finiteWeilCanonicalJointQuantile r k) (volume.restrict (Ioo (0 : ℝ) 1)) =
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) := by
  change Measure.map (finiteWeilCanonicalJointLift r k ∘
    quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ)) _ = _
  rw [← Measure.map_map (finiteWeilCanonicalJointLift_measurable r k) (measurable_quantile _),
    map_quantile_eq, finiteWeilCanonicalJointLift_map]

theorem finiteWeilDiagonalGaussianQuantile_law :
    Measure.map finiteWeilDiagonalGaussianQuantile (volume.restrict (Ioo (0 : ℝ) 1)) =
      (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))) := by
  change Measure.map (finiteWeilDiagonalPoint ∘
    quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ)) _ = _
  rw [← Measure.map_map continuous_finiteWeilDiagonalPoint.measurable (measurable_quantile _),
    map_quantile_eq, finiteWeilDiagonalGaussian_eq_map_projected]

theorem finiteWeilCanonicalJointQuantile_pair_law (r k : ℕ) :
    Measure.map (fun p => (finiteWeilCanonicalJointQuantile r k p, finiteWeilDiagonalGaussianQuantile p))
      (volume.restrict (Ioo (0 : ℝ) 1)) =
      (finiteWeilCanonicalJointGaussianCoupling r k :
        Measure (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) := by
  change Measure.map (fun p => (finiteWeilCanonicalJointQuantile r k p, finiteWeilDiagonalGaussianQuantile p))
    (volume.restrict (Ioo (0 : ℝ) 1)) =
    Measure.map (finiteWeilCanonicalJointGaussianTransportMap r k)
      (monotoneCoupling (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ)
        (finiteWeilProjectedGaussian 1 0 : Measure ℝ))
  rw [monotoneCoupling, Measure.map_map (finiteWeilCanonicalJointGaussianTransportMap_measurable r k)
    (measurable_quantilePair _ _)]
  rfl

theorem finiteWeilCanonicalJointQuantile_at_level (r k : ℕ)
    (p : {p : ℝ // p ∈ Ioo 0 1}) :
    ∃ i, finiteWeilCanonicalJointQuantile r k p.val = finiteWeilCanonicalFluctuationPoint r k i ∧
      quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) p.val =
        finiteWeilCanonicalFluctuationPoint r k i 0 := by
  obtain ⟨i, hi⟩ := finiteWeilCanonicalProjectedIndex_quantile_eq_atom r k p
  refine ⟨i, ?_, hi⟩
  unfold finiteWeilCanonicalJointQuantile
  rw [hi, finiteWeilCanonicalJointLift_at_atom]

theorem finiteWeilCanonicalJointQuantile_fst (r k : ℕ) (p : {p : ℝ // p ∈ Ioo 0 1}) :
    finiteWeilCanonicalJointQuantile r k p.val 0 =
      quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) p.val := by
  obtain ⟨i, hi, hq⟩ := finiteWeilCanonicalJointQuantile_at_level r k p
  rw [hi, hq]

end RHTower
