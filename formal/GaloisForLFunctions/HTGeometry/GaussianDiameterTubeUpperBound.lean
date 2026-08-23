import GaloisForLFunctions.HTGeometry.GaussianDeterminantTubeUpperBound
import GaloisForLFunctions.HTGeometry.GaussianRadialLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Standard Gaussian measure on Euclidean coordinates is globally dominated
by peak density times Lebesgue measure. -/
theorem stdGaussian_le_densityPeak_pow_smul_volume
    (ι : Type) [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) ≤
      gaussianDensityPeakENN ^ Fintype.card ι •
        (volume : Measure (EuclideanSpace ℝ ι)) := by
  rw [stdGaussian_eq_withDensity, ← withDensity_const]
  apply withDensity_mono
  filter_upwards with x
  have hexp : Real.exp (-‖x‖ ^ 2 / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖x‖])
  have hpeak : 0 ≤ gaussianDensityPeak := gaussianDensityPeak_pos.le
  rw [gaussianDensityPeakENN, ← ENNReal.ofReal_pow hpeak]
  apply ENNReal.ofReal_le_ofReal
  unfold euclideanGaussianDensityReal
  exact mul_le_of_le_one_right (pow_nonneg hpeak _) hexp

/-- Gaussian mass of a set is bounded by peak density times its Euclidean
volume. -/
theorem stdGaussian_apply_le_densityPeak_pow_mul_volume
    {ι : Type} [Fintype ι] (S : Set (EuclideanSpace ℝ ι)) :
    stdGaussian (EuclideanSpace ℝ ι) S ≤
      gaussianDensityPeakENN ^ Fintype.card ι * volume S := by
  have h := Measure.le_iff'.mp
    (stdGaussian_le_densityPeak_pow_smul_volume ι) S
  simpa [Measure.smul_apply, smul_eq_mul] using h

/-- A set of diameter at most `R` has at most one Gaussian ball's mass. -/
theorem stdGaussian_apply_le_of_pairwise_dist_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    (S : Set (EuclideanSpace ℝ ι)) {R : ℝ} (_hR : 0 ≤ R)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ R) :
    stdGaussian (EuclideanSpace ℝ ι) S ≤
      gaussianDensityPeakENN ^ Fintype.card ι *
        ((ENNReal.ofReal R) ^ Fintype.card ι *
          ENNReal.ofReal
            (Real.sqrt Real.pi ^ Fintype.card ι /
              Real.Gamma (Fintype.card ι / 2 + 1))) := by
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc⟩ := hS
    have hsub : S ⊆ closedBall c R := by
      intro x hx
      exact mem_closedBall.mpr (hdiam x hx c hc)
    calc
      stdGaussian (EuclideanSpace ℝ ι) S ≤
          stdGaussian (EuclideanSpace ℝ ι) (closedBall c R) :=
        measure_mono hsub
      _ ≤ gaussianDensityPeakENN ^ Fintype.card ι *
          volume (closedBall c R) :=
        stdGaussian_apply_le_densityPeak_pow_mul_volume _
      _ = _ := by rw [EuclideanSpace.volume_closedBall]
  · rw [not_nonempty_iff_eq_empty.mp hS, measure_empty]
    positivity

end

end GaloisForLFunctions.HTGeometry
