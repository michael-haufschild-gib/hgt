import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingFiniteMultiplicity
import GaloisForLFunctions.HTGeometry.FiniteSpectralPhaseActionLaw

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem norm_sub_phaseNormalize_one_eq_abs_norm_sub_one (a : ℂ) :
    ‖a - phaseNormalize 1 a‖ = |‖a‖ - 1| := by
  by_cases ha : a = 0
  · simp [ha, phaseNormalize]
  · rw [phaseNormalize, if_neg ha]
    have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hfac : a - a / ‖a‖ = ((1 - 1 / ‖a‖ : ℝ) : ℂ) * a := by
      push_cast
      field_simp
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [show (1 - 1 / ‖a‖ : ℝ) = (‖a‖ - 1) / ‖a‖ by field_simp]
    rw [abs_div, abs_of_pos hnorm]
    field_simp

theorem tendsto_norm_sub_phaseNormalize_one_zero
    {ι : Type*} {l : Filter ι} (z : ι → ℂ)
    (hz : Tendsto (fun i => ‖z i‖) l (𝓝 1)) :
    Tendsto (fun i => ‖z i - phaseNormalize 1 (z i)‖) l (𝓝 0) := by
  have hsub : Tendsto (fun i => ‖z i‖ - 1) l (𝓝 0) := by
    convert hz.sub_const 1 using 1 <;> norm_num
  have habs := hsub.abs
  have habs' : Tendsto (fun i => |‖z i‖ - 1|) l (𝓝 0) := by simpa using habs
  exact habs'.congr' (Eventually.of_forall fun i =>
    (norm_sub_phaseNormalize_one_eq_abs_norm_sub_one (z i)).symm)

theorem tendsto_norm_finiteModelResidualCore_repeatSingle_zero_of_norm_value_one
    {ι : Type*} {l : Filter ι} (F : ι → DiskMultiplier)
    (hF : ∀ i, HardyMultiplierIsometry (F i))
    (q : ι → ℂ) (hq : ∀ i, ‖q i‖ < 1) (m : ℕ)
    (hvalue : Tendsto (fun i => ‖(F i).fn (q i)‖) l (𝓝 1)) :
    Tendsto (fun i =>
      ‖finiteModelResidualCore (F i) (FiniteBlaschke.repeatSingle (hq i) m)
        (phaseNormalize 1 ((F i).fn (q i)))‖) l (𝓝 0) := by
  apply tendsto_norm_finiteModelResidualCore_repeatSingle_zero
    F hF q hq (fun i => phaseNormalize 1 ((F i).fn (q i)))
  · intro i
    exact norm_phaseNormalize_finiteSpectralPhaseActionLaw (by norm_num)
  · exact tendsto_norm_sub_phaseNormalize_one_zero
      (fun i => (F i).fn (q i)) hvalue

end

end GaloisForLFunctions.HTGeometry
