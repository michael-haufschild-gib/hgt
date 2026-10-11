import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileLaw
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Actual finite joint laws are essentially bounded; their diagonal Gaussian
limit is essentially unbounded. -/

open MeasureTheory ProbabilityTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilCanonicalJointQuantile_memLp_top (r k : ℕ) :
    MemLp (finiteWeilCanonicalJointQuantile r k) ⊤ (volume.restrict (Ioo (0 : ℝ) 1)) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun i : Fin (r + 1) =>
    ‖finiteWeilCanonicalFluctuationPoint r k i‖)
  apply memLp_top_of_bound (finiteWeilCanonicalJointQuantile_measurable r k).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  obtain ⟨i, hi, _⟩ := finiteWeilCanonicalJointQuantile_at_level r k ⟨u, hu⟩
  rw [hi]
  exact hC i

theorem finiteWeilCanonicalJointProbabilityLaw_id_memLp_top (r k : ℕ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x) ⊤
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure _) := by
  have hmap := memLp_map_measure_iff (μ := volume.restrict (Ioo (0 : ℝ) 1)) (p := ⊤)
    (g := fun x : EuclideanSpace ℝ (Fin 2) => x) measurable_id.aestronglyMeasurable
    (finiteWeilCanonicalJointQuantile_measurable r k).aemeasurable
  rw [finiteWeilCanonicalJointQuantile_law] at hmap
  exact hmap.mpr (finiteWeilCanonicalJointQuantile_memLp_top r k)

theorem finiteWeil_gaussian_not_ae_bounded_above (m : ℝ) (v : NNReal) (hv : v ≠ 0) (C : ℝ) :
    ¬ ∀ᵐ x ∂(gaussianReal m v), x ≤ C := by
  intro h
  have hvol : ∀ᵐ x ∂(volume : Measure ℝ), x ≤ C :=
    (gaussianReal_absolutelyContinuous' m hv).ae_le h
  have hset : {x : ℝ | ¬ x ≤ C} = Ioi C := by
    ext x
    exact not_le
  have hz : (volume : Measure ℝ) (Ioi C) = 0 := by
    rw [← hset]
    exact ae_iff.mp hvol
  rw [Real.volume_Ioi] at hz
  exact ENNReal.top_ne_zero hz

theorem finiteWeilDiagonalGaussian_id_not_memLp_top :
    ¬ MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x) ⊤
      (finiteWeilDiagonalGaussian : Measure _) := by
  intro h
  change MemLp (fun x : EuclideanSpace ℝ (Fin 2) => x) ⊤
    (Measure.map finiteWeilDiagonalPoint (gaussianReal 0 (1 / 4))) at h
  have hp := (memLp_map_measure_iff (μ := gaussianReal 0 (1 / 4)) (p := ⊤)
    (g := fun x : EuclideanSpace ℝ (Fin 2) => x) measurable_id.aestronglyMeasurable
    continuous_finiteWeilDiagonalPoint.measurable.aemeasurable).mp h
  change MemLp finiteWeilDiagonalPoint ⊤ (gaussianReal 0 (1 / 4)) at hp
  have hfin : eLpNormEssSup finiteWeilDiagonalPoint (gaussianReal 0 (1 / 4)) < ⊤ := by
    simpa only [eLpNorm_exponent_top] using hp.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hfin
  apply finiteWeil_gaussian_not_ae_bounded_above 0 (1 / 4) (by norm_num) (C : ℝ)
  filter_upwards [hC] with x hx
  have hxnorm : ‖finiteWeilDiagonalPoint x‖ ≤ (C : ℝ) := by exact_mod_cast hx
  have hc := PiLp.norm_apply_le (finiteWeilDiagonalPoint x) (0 : Fin 2)
  change ‖x‖ ≤ ‖finiteWeilDiagonalPoint x‖ at hc
  rw [Real.norm_eq_abs] at hc
  exact (le_abs_self x).trans (hc.trans hxnorm)

end RHTower
