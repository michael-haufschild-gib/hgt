import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspNativeMeanSquare

/-! The actual cusp mean inherits finite mass from the original native Hilbert response. -/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

/-- The actual width-one response mean obeys the sharp Cauchy-Schwarz contraction. -/
theorem responseMean_norm_sq_le (q : XiZeroCopy) (branch : Bool) {y : ℝ} (hy : 0 < y) :
    ‖responseMean q branch y‖^(2 : ℕ) ≤ responseMeanSquare q branch y := by
  have hf := slice_continuous (responsePlanar q branch) (responsePlanar_smooth q branch) hy
  have h := integral_norm_le_sqrt_length_mul_sqrt_meanSquare hf
    (a := (-1/2:ℝ)) (b := (1/2:ℝ)) (by norm_num)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2),
    intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ)≤1/2)] at h
  norm_num only [show (1/2:ℝ)-(-1/2)=1 by norm_num,Real.sqrt_one,one_mul] at h
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Ioc (-1/2:ℝ) (1/2)))
    (f := fun x => responsePlanar q branch (point x y))
  have hm : ‖responseMean q branch y‖ ≤ Real.sqrt (responseMeanSquare q branch y) :=
    hn.trans (by simpa only [responseMeanSquare,neg_div] using h)
  have hs : 0 ≤ responseMeanSquare q branch y := integral_nonneg (fun x => sq_nonneg _)
  calc
    ‖responseMean q branch y‖^(2 : ℕ) ≤ (Real.sqrt (responseMeanSquare q branch y))^(2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hm
    _ = responseMeanSquare q branch y := Real.sq_sqrt hs

/-- The original native Hilbert norm forces square-integrability of the actual cusp mean. -/
theorem responseMean_density_integrable (q : XiZeroCopy) (branch : Bool) :
    IntegrableOn (fun y : ℝ => ‖responseMean q branch y‖^(2 : ℕ)/y^(2 : ℕ)) (Ioi (2:ℝ)) := by
  have hc : ContinuousOn (fun y : ℝ => ‖responseMean q branch y‖^(2 : ℕ)/y^(2 : ℕ)) (Ioi (2:ℝ)) := by
    intro y hy
    have hp : 0 < y := by change 2 < y at hy; linarith
    exact (((average_hasDerivAt (responsePlanar q branch) (responsePlanar_smooth q branch) hp).continuousAt.norm.pow 2).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 hp.ne')).continuousWithinAt
  apply (responseMeanSquare_density_integrable q branch).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  exact div_le_div_of_nonneg_right (responseMean_norm_sq_le q branch (by change 2 < y at hy; linarith)) (sq_nonneg y)

end
end RHTower.D4BMCuspResponse
