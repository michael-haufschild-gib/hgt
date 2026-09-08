import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceKernelBounds
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! Absolute convergence of the actual retained-source endpoint integrals. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMLaplaceRadial
noncomputable section

attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Actual source continuity, including both radial endpoints in the time chamber. -/
theorem sourceProfile_continuous {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    Continuous (sourceProfile s w a J K T) := by
  have hw : 0 < (w/2).re := by simpa using half_pos (chamber_re_pos h)
  exact (Complex.continuous_ofReal_cpow_const hw).mul (sourceRemainder_continuous s w a J K T)

/-- Continuity of both actual Green integrands in the physical interior. -/
theorem sourceIntegrands_continuousOn {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    ContinuousOn (fun z => horizon w chi z*sourceProfile s w a J K T z) (Ioo 0 1) ∧
    ContinuousOn (fun z => normalizable w chi z*sourceProfile s w a J K T z) (Ioo 0 1) := by
  have hS := sourceProfile_continuous h s a J K T
  constructor <;> intro z hz
  · exact ((horizon_derivatives h hz).1.continuousAt.mul hS.continuousAt).continuousWithinAt
  · exact ((normalizable_derivatives h hz).1.continuousAt.mul hS.continuousAt).continuousWithinAt

private theorem integrable_of_power_bound {f : ℝ → ℂ} (hc : ContinuousOn f (Ioo 0 1))
    {b : ℝ} (hb : -1 < b) (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, z ∈ Ioo 0 1 → ‖f z‖ ≤ C*z^b) :
    IntegrableOn f (Ioo 0 1) := by
  obtain ⟨C,-,hC⟩ := hbound
  have hi := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0:ℝ)<1 by norm_num)).mpr hb
  refine (hi.const_mul C).mono' (hc.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact hC z hz

/-- Both genuine endpoint Green integrals converge absolutely on (0,1), for
all independent chamber frequencies and the full original source profile.
No integrability premise or nonresonance assumption is supplied. -/
theorem sourceIntegrands_integrable {w chi : ℂ} (h : Chamber w chi) (s a J K T : ℂ) :
    IntegrableOn (fun z => horizon w chi z*sourceProfile s w a J K T z) (Ioo 0 1) ∧
    IntegrableOn (fun z => normalizable w chi z*sourceProfile s w a J K T z) (Ioo 0 1) := by
  have hc := sourceIntegrands_continuousOn h s a J K T
  constructor
  · exact integrable_of_power_bound hc.1 (by linarith [chamber_re_pos h]) (horizon_source_bound h s a J K T)
  · let N := Nat.ceil w.re
    have hN : 1 ≤ N := Nat.one_le_ceil_iff.mpr (chamber_re_pos h)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hN))
    have hkle : w.re-1 ≤ (k:ℝ) := by
      have hn := Nat.le_ceil w.re
      change w.re ≤ (N:ℝ) at hn
      rw [hk] at hn
      push_cast at hn
      linarith
    have hklt : -1 < w.re-((k+1:ℕ):ℝ) := by
      have hn := Nat.ceil_lt_add_one (chamber_re_pos h).le
      change (N:ℝ) < w.re+1 at hn
      rw [hk] at hn
      linarith
    exact integrable_of_power_bound hc.2 hklt (normalizable_source_bound h s a J K T k hkle)

end
end RHTower.D4BMLaplaceRadial
