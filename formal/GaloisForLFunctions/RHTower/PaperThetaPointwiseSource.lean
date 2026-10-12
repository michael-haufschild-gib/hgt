import GaloisForLFunctions.RHTower.PaperThetaLocalFourier

/-! # Pointwise recovery of the original source and a strict logarithmic endpoint witness -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace RHTower.PaperThetaEndpoint

open HedenmalmThetaSource GaloisForLFunctions.HTGeometry FourierLLogL

theorem integrable_flatMode_iff_all (z : ℂ) :
    Integrable (flatMode z) ↔ z = 0 ∨ XiC z = 0 ∨ 0 < z.im := by
  rw [← integrable_norm_iff (continuous_flatMode_all z).aestronglyMeasurable]
  have he : logPowerDensity z 0 = fun x => ‖flatMode z x‖ := by
    funext x
    simp only [logPowerDensity, NNReal.coe_zero, Real.rpow_zero, mul_one]
  simpa only [he, NNReal.coe_zero, mul_zero] using integrable_logPowerDensity_iff z 0

theorem integrable_sourceCoeff_L1 (z : L1Point) (k : ℤ) :
    Integrable (fun x => flatMode z.val x * Period.phase (-k) (thetaSource.cdfFun x)) := by
  have hu := (integrable_flatMode_iff_all z.val).mpr z.property
  refine hu.norm.mono' (hu.aestronglyMeasurable.mul
    ((Period.phase_cont (-k)).comp thetaSource.continuous_cdfFun).aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Period.phase_unimod, mul_one]

/-- Exact full symmetric source coefficients recover every interior quantile point. -/
theorem source_quantile_recovery_L1 (z : L1Point) (t : Ioo (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => sourcePartialSum z.val N t.val) atTop
      (𝓝 (flatModePullback z.val t.val)) := by
  simpa only [sourcePartialSum_eq_all] using circle_interior_recovery_L1 z t

/-- The original source amplitude is recovered at every real coordinate, without a null set. -/
theorem source_flat_recovery_L1 (z : L1Point) (x : ℝ) :
    Tendsto (fun N : ℕ => (thetaSource.normalized x : ℂ) *
      sourcePartialSum z.val N (thetaSource.cdfFun x)) atTop (𝓝 (flatMode z.val x)) := by
  have h := (source_quantile_recovery_L1 z
    ⟨thetaSource.cdfFun x, thetaSource.cdfFun_mem_Ioo x⟩).const_mul (thetaSource.normalized x : ℂ)
  convert h using 1
  rw [flatModePullback_eq_flatQuotient, thetaSource.quantile_cdfFun, flatQuotient]
  have hρ : (thetaSource.normalized x : ℂ) ≠ 0 := by
    exact_mod_cast (thetaSource.normalized_pos x).ne'
  field_simp

/-- The concrete parameter at imaginary height two fails the paper's L log L admission. -/
theorem twoI_not_memLLogL : ¬ MemLLogL (circleMode (2*Complex.I)) := by
  rw [memLLogL_circleMode_iff_all]
  rintro (h0 | hXi | hgt)
  · have h := congrArg Complex.im h0
    norm_num at h
  · have h := abs_im_lt_one_of_XiC_eq_zero hXi
    norm_num at h
  · norm_num at hgt

/-- Failure of logarithmic admission does not prevent actual pointwise source recovery. -/
theorem twoI_pointwise_recovery :
    ¬ MemLLogL (circleMode (2*Complex.I)) ∧ ∀ x : ℝ,
      Tendsto (fun N : ℕ => (thetaSource.normalized x : ℂ) *
        sourcePartialSum (2*Complex.I) N (thetaSource.cdfFun x))
        atTop (𝓝 (flatMode (2*Complex.I) x)) := by
  refine ⟨twoI_not_memLLogL, fun x => ?_⟩
  exact source_flat_recovery_L1 ⟨2*Complex.I, Or.inr (Or.inr (by norm_num))⟩ x

end RHTower.PaperThetaEndpoint
