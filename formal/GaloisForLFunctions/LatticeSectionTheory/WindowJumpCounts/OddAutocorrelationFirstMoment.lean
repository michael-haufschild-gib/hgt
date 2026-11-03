import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddAutocorrelationSecondMoment
import GaloisForLFunctions.ArithmeticCompensationTheory.TheResolventIdentityAndSecondHorizonCorrection
import GaloisForLFunctions.HTGeometry.CompactPrimitive

/-!
# The first odd correlation moment

The linear lag moment is minus the squared norm of the compact primitive.
Together with the second moment, this retains the source-dependent Gamma costs.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.LatticeSectionTheory
open ArithmeticCriticalityTheory ArithmeticIncidencePositivity ArithmeticCompensationTheory

/-- The linear correlation moment of a derivative is minus the primitive mass. -/
theorem derivative_autocorr_first_moment {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H)
    (hcs : HasCompactSupport H) :
    (∫ t in Ioi (0 : ℝ), t * autocorr (deriv H) t) = -(∫ x, H x ^ 2) := by
  let W : ℝ → ℝ := fun t => autoCorr H t - t * crossCorr H t
  have hAd : deriv (autoCorr H) = crossCorr H :=
    funext fun t => (hasDerivAt_autoCorr hH hcs t).deriv
  have hAc : HasCompactSupport (autoCorr H) := hasCompactSupport_autocorr hcs
  have hKc : HasCompactSupport (crossCorr H) := by
    rw [← hAd]
    exact hAc.deriv
  have hWc : HasCompactSupport W := hAc.sub hKc.mul_left
  have hWd (t : ℝ) : HasDerivAt W (t * autoCorr (deriv H) t) t := by
    refine ((hasDerivAt_autoCorr hH hcs t).sub
      ((hasDerivAt_id t).mul (hasDerivAt_crossCorr hH hcs t))).congr_deriv ?_
    ring
  have hWe : deriv W = fun t => t * autoCorr (deriv H) t :=
    funext fun t => (hWd t).deriv
  have hW1 : ContDiff ℝ 1 W := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t => (hWd t).differentiableAt, ?_⟩
    rw [hWe]
    exact continuous_id.mul (continuous_autoCorr (hH.continuous_deriv le_rfl) hcs.deriv)
  have h := HasCompactSupport.integral_Ioi_deriv_eq hW1 hWc 0
  rw [hWe] at h
  simpa only [W, zero_mul, sub_zero, autoCorr_zero_eq_integral_sq] using h

/-- The primitive from the fixed left endpoint `−1` of a unit-window source. -/
def unitSourcePrimitive (F : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in (-1 : ℝ)..x, F y

private theorem unit_odd_primitive_regular {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    ContDiff ℝ 1 (unitSourcePrimitive F) ∧ HasCompactSupport (unitSourcePrimitive F) ∧
      deriv (unitSourcePrimitive F) = F := by
  have hd (x : ℝ) : HasDerivAt (unitSourcePrimitive F) (F x) x :=
    (hF.integral_hasStrictDerivAt (-1) x).hasDerivAt
  have he : deriv (unitSourcePrimitive F) = F := funext fun x => (hd x).deriv
  have h1 : ContDiff ℝ 1 (unitSourcePrimitive F) := by
    apply contDiff_one_iff_deriv.mpr
    exact ⟨fun x => (hd x).differentiableAt, by rw [he]; exact hF⟩
  have hz : ∀ x, x ∉ Ioo (-1 : ℝ) 1 → F x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hi := hs ht
    exact hx ⟨by linarith only [hi.1], by linarith only [hi.2]⟩
  have hm : (∫ x, F x) = 0 := by
    have h := integral_neg_eq_self F volume
    rw [integral_congr_ae (Eventually.of_forall ho), integral_neg] at h
    linarith only [h]
  have hmi : (∫ x in (-1 : ℝ)..1, F x) = 0 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hz x (fun hi => hx ⟨hi.1, hi.2.le⟩)), hm]
  have hp := HTGeometry.primitive_eq_zero_outside hF hz hmi
  have hc : HasCompactSupport (unitSourcePrimitive F) := by
    apply HasCompactSupport.intro (K := Icc (-1 : ℝ) 1) isCompact_Icc
    intro x hx
    exact hp x (fun hi => hx (Ioo_subset_Icc_self hi))
  exact ⟨h1, hc, he⟩

/-- Oddness gives a compact primitive, whose mass is the negative first correlation moment. -/
theorem unit_odd_autocorr_first_moment {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, t * autocorr F t) =
      -(∫ x, unitSourcePrimitive F x ^ 2) := by
  obtain ⟨hP, hPc, hPd⟩ := unit_odd_primitive_regular hF hs ho
  have h := derivative_autocorr_first_moment hP hPc
  rw [hPd] at h
  have hcut : (∫ t in Ioi (0 : ℝ), t * autocorr F t) =
      ∫ t in Ioc (0 : ℝ) 1, t * autocorr F t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), t * autocorr F t =
        (Iic (1 : ℝ)).indicator (fun t => t * autocorr F t) t := by
      intro t _ht
      by_cases ht : t ≤ 1
      · exact (Set.indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht)
          (fun t => t * autocorr F t)).symm
      · rw [Set.indicator_of_notMem (show t ∉ Iic (1 : ℝ) from ht),
          autocorr_eq_zero_of_support hs (by norm_num; exact lt_of_not_ge ht), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic]
  rw [hcut] at h
  exact h

/-- The first unit-window jump cost is half the source mass plus its primitive mass. -/
theorem unit_odd_jump_first_moment {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, t * (autocorr F 0 - autocorr F t)) =
      autocorr F 0 / 2 + (∫ x, unitSourcePrimitive F x ^ 2) := by
  have hcs : HasCompactSupport F := HasCompactSupport.intro isCompact_Icc
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)))
  have hc : Continuous (autocorr F) := continuous_autoCorr hF hcs
  have hp : (∫ t in Ioc (0 : ℝ) 1, t) = (1 / 2 : ℝ) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
    norm_num
  have hi0 : IntegrableOn (fun t : ℝ => t * autocorr F 0) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi1 : IntegrableOn (fun t : ℝ => t * autocorr F t) (Ioc (0 : ℝ) 1) :=
    (continuous_id.mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simp_rw [mul_sub]
  rw [integral_sub hi0 hi1, integral_mul_const, hp,
    unit_odd_autocorr_first_moment hF hs ho]
  ring

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.derivative_autocorr_first_moment
#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_odd_autocorr_first_moment
#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_odd_jump_first_moment
