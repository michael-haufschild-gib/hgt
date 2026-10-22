import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceAmplitude
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointRadialCore
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Genuine L² admission on the infinite tortoise half-line from the independent Laplace damping. -/
open MeasureTheory Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMLaplaceRadial
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Every continuous compact-radius profile times the independent Laplace exponential is in
L² on the entire physical tortoise half-line, including the horizon. -/
theorem laplaceProfile_memLp (w : ℂ) (hw : 0 < w.re) (F : ℝ → ℂ)
    (hF : ContinuousOn F (Icc 0 1)) :
    MemLp (fun t : ℝ => Complex.exp (w*(t:ℂ))*F (radialUnit t)) 2 radialMeasure := by
  have hU : Continuous radialUnit := continuous_iff_continuousAt.mpr
    (fun t => (radialUnit_hasDerivAt t).continuousAt)
  have hC : ContinuousOn (fun t : ℝ => Complex.exp (w*(t:ℂ))*F (radialUnit t)) (Iio 0) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (w*(t:ℂ)))).continuousOn.mul
      (hF.comp hU.continuousOn (fun t ht =>
        ⟨(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩))
  have hI : Integrable (fun t : ℝ => Real.exp ((2*w.re)*t)) radialMeasure :=
    (integrableOn_exp_mul_Iic (by linarith : 0 < 2*w.re) 0).mono_set Iio_subset_Iic_self
  have hE : MemLp (fun t : ℝ => Real.exp (w.re*t)) 2 radialMeasure := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    apply hI.congr
    filter_upwards [] with t
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  obtain ⟨C,hbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hF
  let B := max C 0
  have hB : 0 ≤ B := le_max_right _ _
  apply MemLp.of_le (hE.const_mul B) (hC.aestronglyMeasurable measurableSet_Iio)
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  have hb : ‖F (radialUnit t)‖ ≤ B :=
    (hbound _ ⟨(radialUnit_bounds t ht).1.le,(radialUnit_bounds t ht).2.le⟩).trans (le_max_left _ _)
  rw [norm_mul,Complex.norm_exp]
  have hre : (w*(t:ℂ)).re = w.re*t := by simp
  rw [hre]
  calc
    Real.exp (w.re*t)*‖F (radialUnit t)‖ ≤ Real.exp (w.re*t)*B :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ‖B*Real.exp (w.re*t)‖ := by rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hB (Real.exp_pos _).le)]; ring

/-- The actual source amplitude times any compact-radius continuous factor is admitted, with
all physical-rate, amplitude, and onset factors retained. -/
theorem sourceAmplitude_profile_memLp (s w a T : ℂ) (hw : 0 < w.re) (P : ℝ → ℂ)
    (hP : ContinuousOn P (Icc 0 1)) :
    MemLp (fun t => sourceAmplitude s w a T t*P (radialUnit t)) 2 radialMeasure := by
  have hpower : ContinuousOn (fun u : ℝ => power (2*s) (1+u)) (Icc 0 1) := by
    intro u hu
    have hp := (power_derivatives (2*s) (by linarith [hu.1] : 0 < 1+u)).1.continuousAt
    exact (hp.comp_of_eq (continuous_const.add continuous_id).continuousAt rfl).continuousWithinAt
  have h := laplaceProfile_memLp w hw (fun u => power (2*s) (1+u)*a^(2 : ℕ)*T*P u)
    (((hpower.mul continuousOn_const).mul continuousOn_const).mul hP)
  convert! h using 1
  ext t
  dsimp [sourceAmplitude]
  ring

end
end RHTower.D4BMJointSource
