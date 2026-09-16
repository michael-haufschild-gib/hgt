import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteOriginalWeakSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceTimeTranslation

/-!
# Full-field weak onset transgression

The literal cap-corrected future field has an exact compact-test weak equation.
This leaf transports that equation under a physical-time translation.  The
translation defect has the exact original fixed-onset forcing defect, with no
change of source rate, causal kernel, cap, or test support condition.
-/

open MeasureTheory Set Filter Topology
namespace RHTower.D4BMFullFieldOnsetTransgression

open D4BMGeneralTemporalTransposition
open D4BMAdvancedKernelTransposition D4BMFullSourceWeakWave D4BMFullSourceAdvanced
open D4BMCausalKernel D4BMModularCore D4BMCompleteOriginalWeakSource
open D4BMSourceTimeTranslation D4BMJointSource
open scoped ContDiff ENNReal
noncomputable section
set_option autoImplicit false

def timeShift (T : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := p - (T, 0)

private theorem eventDir_timeShift (T : ℝ) (phi : ℝ × ℝ → ℂ)
    (hphi : ContDiff ℝ ∞ phi) (v p : ℝ × ℝ) :
    eventDir v (fun r => phi (timeShift T r)) p =
      eventDir v phi (timeShift T p) := by
  have hshift := (hasFDerivAt_id (𝕜 := ℝ) p).sub_const (T, 0)
  have hphi' := (hphi.differentiable (by simp) (timeShift T p)).hasFDerivAt
  have hcomp := hphi'.comp p hshift
  have hf : fderiv ℝ (fun r : ℝ × ℝ => phi (timeShift T r)) p =
      fderiv ℝ phi (timeShift T p) := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using hcomp.fderiv
  unfold eventDir
  rw [hf]

private theorem eventDir_smooth {phi : ℝ × ℝ → ℂ} (hphi : ContDiff ℝ ∞ phi) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (eventDir v phi) :=
  (hphi.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem eventWave_timeShift (T : ℝ) (phi : ℝ × ℝ → ℂ)
    (hphi : ContDiff ℝ ∞ phi) (p : ℝ × ℝ) :
    eventWave (fun r => phi (timeShift T r)) p = eventWave phi (timeShift T p) := by
  have hfirst (v : ℝ × ℝ) :
      eventDir v (fun r => phi (timeShift T r)) = fun r => eventDir v phi (timeShift T r) := by
    funext r
    exact eventDir_timeShift T phi hphi v r
  unfold eventWave
  rw [hfirst (1,0),hfirst (0,1)]
  rw [eventDir_timeShift T (eventDir (1,0) phi) (eventDir_smooth hphi (1,0)) (1,0) p,
    eventDir_timeShift T (eventDir (0,1) phi) (eventDir_smooth hphi (0,1)) (0,1) p]

def targetTimeShift (T : ℝ) (r : (ℝ × ℝ) × ℂ) : (ℝ × ℝ) × ℂ := r - ((T,0),0)

private theorem targetTimeShift_mk (T : ℝ) (r : ℝ × ℝ) (z : ℂ) :
    targetTimeShift T (r,z) = (timeShift T r,z) := by
  simp only [targetTimeShift,timeShift,Prod.mk_sub_mk,sub_zero]

private theorem targetTimeShift_add_mk (T : ℝ) (p : (ℝ × ℝ) × ℂ) :
    targetTimeShift T (p + ((T,0),0)) = p := by
  simp only [targetTimeShift,add_sub_cancel_right]

private theorem timeShift_add (T : ℝ) (r : ℝ × ℝ) : timeShift T (r + (T,0)) = r := by
  simp only [timeShift,add_sub_cancel_right]

private def translatedTest (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ) : (ℝ × ℝ) × ℂ → ℂ :=
  fun r => F (targetTimeShift T r)

private def targetTimeShiftHomeomorph (T : ℝ) : ((ℝ × ℝ) × ℂ) ≃ₜ ((ℝ × ℝ) × ℂ) where
  toFun := targetTimeShift T
  invFun := fun r => r + ((T,0),0)
  left_inv r := sub_add_cancel r ((T,0),0)
  right_inv r := add_sub_cancel_right r ((T,0),0)
  continuous_toFun := continuous_id.sub continuous_const
  continuous_invFun := continuous_id.add continuous_const

private theorem translatedTest_compact (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ)
    (hF : HasCompactSupport F) : HasCompactSupport (translatedTest T F) := by
  change HasCompactSupport (F ∘ targetTimeShift T)
  exact hF.comp_homeomorph (targetTimeShiftHomeomorph T)

private theorem targetTimeShift_smooth (T : ℝ) : ContDiff ℝ ∞ (targetTimeShift T) := by
  unfold targetTimeShift
  exact contDiff_id.sub contDiff_const

private theorem translatedTest_smooth (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ)
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (translatedTest T F) := by
  exact hF.comp (targetTimeShift_smooth T)

private theorem targetTimeShift_radial (T : ℝ) (r : (ℝ × ℝ) × ℂ) :
    (targetTimeShift T r).1.2 = r.1.2 := by
  simp only [targetTimeShift,Prod.fst_sub,Prod.snd_sub,sub_zero]

private theorem translatedTest_tsupport_map (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ)
    (r : (ℝ × ℝ) × ℂ) (hr : r ∈ tsupport (translatedTest T F)) :
    targetTimeShift T r ∈ tsupport F := by
  have himage : targetTimeShift T '' Function.support (translatedTest T F) = Function.support F := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change translatedTest T F x ≠ 0 at hx
      change F (targetTimeShift T x) ≠ 0
      simpa only [translatedTest] using hx
    · intro hy
      refine ⟨(targetTimeShiftHomeomorph T).symm y,?_,?_⟩
      · change translatedTest T F ((targetTimeShiftHomeomorph T).symm y) ≠ 0
        change F (targetTimeShift T ((targetTimeShiftHomeomorph T).symm y)) ≠ 0
        have hshift : targetTimeShift T ((targetTimeShiftHomeomorph T).symm y) = y := by
          change (targetTimeShiftHomeomorph T) ((targetTimeShiftHomeomorph T).symm y) = y
          exact (targetTimeShiftHomeomorph T).apply_symm_apply y
        rw [hshift]
        exact hy
      · exact (targetTimeShiftHomeomorph T).apply_symm_apply y
  change r ∈ closure (Function.support (translatedTest T F)) at hr
  change targetTimeShift T r ∈ closure (Function.support F)
  have hrimage : (targetTimeShiftHomeomorph T) r ∈
      (targetTimeShiftHomeomorph T) '' closure (Function.support (translatedTest T F)) := ⟨r,hr,rfl⟩
  rw [(targetTimeShiftHomeomorph T).isHomeomorph.image_closure] at hrimage
  have himageHomeo : (targetTimeShiftHomeomorph T) '' Function.support (translatedTest T F) =
      Function.support F := by
    change targetTimeShift T '' Function.support (translatedTest T F) = Function.support F
    exact himage
  rw [himageHomeo] at hrimage
  exact hrimage

private theorem translatedTest_physical (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ)
    (hphysical : tsupport F ⊆ {r : (ℝ × ℝ) × ℂ | r.1.2 < 0}) :
    tsupport (translatedTest T F) ⊆ {r : (ℝ × ℝ) × ℂ | r.1.2 < 0} := by
  intro r hr
  have h := hphysical (translatedTest_tsupport_map T F r hr)
  change (targetTimeShift T r).1.2 < 0 at h
  rw [targetTimeShift_radial] at h
  exact h

private theorem weakWaveTest_timeShift (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ)
    (hF : ContDiff ℝ ∞ F) (p : (ℝ × ℝ) × ℂ) :
    weakWaveTest (translatedTest T F) (p + ((T,0),0)) = weakWaveTest F p := by
  have hslice : ContDiff ℝ ∞ (fun r : ℝ × ℝ => F (r,p.2)) :=
    hF.comp (contDiff_id.prodMk contDiff_const)
  have hplus_fst : (p + ((T,0),0)).1 = p.1 + (T,0) := rfl
  have hplus_snd : (p + ((T,0),0)).2 = p.2 := by simp only [Prod.snd_add,add_zero]
  have hevent_fun :
      (fun r => translatedTest T F (r,(p + ((T,0),0)).2)) =
        fun r => F (timeShift T r,p.2) := by
    funext r
    simp only [translatedTest,Prod.snd_add,add_zero]
    rw [targetTimeShift_mk]
  have hevent :
      eventWave (fun r => translatedTest T F (r,(p + ((T,0),0)).2))
        (p + ((T,0),0)).1 = eventWave (fun r => F (r,p.2)) p.1 := by
    rw [hevent_fun,hplus_fst]
    rw [eventWave_timeShift T (fun r => F (r,p.2)) hslice]
    exact congrArg (eventWave (fun r => F (r,p.2))) (timeShift_add T p.1)
  have hangular_fun :
      (fun z => translatedTest T F ((p + ((T,0),0)).1,z)) = fun z => F (p.1,z) := by
    funext z
    rw [hplus_fst]
    change F (targetTimeShift T (p.1 + (T,0),z)) = F (p.1,z)
    rw [targetTimeShift_mk,timeShift_add]
  have hradial : (p.1 + (T,0)).2 = p.1.2 := by
    simp only [Prod.snd_add,add_zero]
  unfold weakWaveTest
  rw [hevent,hangular_fun,hplus_fst,hplus_snd,hradial]

private theorem target_volume_isAddRightInvariant :
    (volume : Measure ((ℝ × ℝ) × ℂ)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

private theorem weak_pair_timeShift_left (T : ℝ) (U F : (ℝ × ℝ) × ℂ → ℂ)
    (hF : ContDiff ℝ ∞ F) :
    (∫ r : (ℝ × ℝ) × ℂ, U r * weakWaveTest (translatedTest T F) r) =
      ∫ r : (ℝ × ℝ) × ℂ, U (r + ((T,0),0)) * weakWaveTest F r := by
  letI : (volume : Measure ((ℝ × ℝ) × ℂ)).IsAddRightInvariant := target_volume_isAddRightInvariant
  rw [← integral_add_right_eq_self (fun r : (ℝ × ℝ) × ℂ =>
    U r * weakWaveTest (translatedTest T F) r) ((T,0),0)]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    change U (r + ((T,0),0)) * weakWaveTest (translatedTest T F) (r + ((T,0),0)) =
      U (r + ((T,0),0)) * weakWaveTest F r
    rw [weakWaveTest_timeShift T F hF r])

private theorem source_pair_timeShift_right (T : ℝ) (S F : (ℝ × ℝ) × ℂ → ℂ) :
    (∫ r : (ℝ × ℝ) × ℂ, S r * translatedTest T F r) =
      ∫ r : (ℝ × ℝ) × ℂ, S (r + ((T,0),0)) * F r := by
  letI : (volume : Measure ((ℝ × ℝ) × ℂ)).IsAddRightInvariant := target_volume_isAddRightInvariant
  rw [← integral_add_right_eq_self (fun r : (ℝ × ℝ) × ℂ =>
    S r * translatedTest T F r) ((T,0),0)]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    change S (r + ((T,0),0)) * F (targetTimeShift T (r + ((T,0),0))) =
      S (r + ((T,0),0)) * F r
    rw [targetTimeShift_add_mk])

def originalForcingDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (r : (ℝ × ℝ) × ℂ) : ℂ :=
  (Real.exp (-r.2.im):ℂ)*
    timeOriginalForcing q branch a r.1.1 r.1.2 ![r.2.re,Real.exp r.2.im]

/-- The exact full original source left by a finite fixed-onset time translation. -/
def onsetDefectForcingDensity (q : XiZeroCopy) (branch : Bool) (a : ℂ) (T : ℝ)
    (r : (ℝ × ℝ) × ℂ) : ℂ :=
  (Real.exp (-r.2.im):ℂ)*
    originalForcing (physicalRate q branch) 0 a 1
      (fullSquarePotential q ![r.2.re,Real.exp r.2.im])
      (fullGradientEnergy q ![r.2.re,Real.exp r.2.im]/2) r.1.2*
    onsetDefect (2*physicalRate q branch) T (r.1.1+r.1.2)

theorem originalForcingDensity_translation (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (T : ℝ) (r : (ℝ × ℝ) × ℂ) :
    originalForcingDensity q branch a (r + ((T,0),0))-
      sourceFactor q branch T*originalForcingDensity q branch a r =
        onsetDefectForcingDensity q branch a T r := by
  simp only [originalForcingDensity,onsetDefectForcingDensity,Prod.fst_add,Prod.snd_add,add_zero]
  calc
    _ = (Real.exp (-r.2.im):ℂ)*
        (timeOriginalForcing q branch a (r.1.1+T) r.1.2 ![r.2.re,Real.exp r.2.im]-
          sourceFactor q branch T*timeOriginalForcing q branch a r.1.1 r.1.2
            ![r.2.re,Real.exp r.2.im]) := by ring
    _ = _ := by
      rw [originalForcing_translation]
      ring

/-- Translation of the literal cap-corrected full field is a weak solution for
the correspondingly translated literal original source. -/
theorem complete_original_weak_wave_timeShift (q : XiZeroCopy) (branch : Bool) (a : ℂ) (T : ℝ)
    (F : (ℝ × ℝ) × ℂ → ℂ) (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : (ℝ × ℝ) × ℂ | r.1.2 < 0}) :
    (∫ r : (ℝ × ℝ) × ℂ,
      correctedFutureField q branch a (r + ((T,0),0))*weakWaveTest F r) =
      ∫ r : (ℝ × ℝ) × ℂ, originalForcingDensity q branch a (r + ((T,0),0))*F r := by
  have hbase := complete_original_weak_wave q branch a (translatedTest T F)
    (translatedTest_smooth T F hF) (translatedTest_compact T F hc)
    (translatedTest_physical T F hphysical)
  calc
    (∫ r : (ℝ × ℝ) × ℂ,
      correctedFutureField q branch a (r + ((T,0),0))*weakWaveTest F r) =
        ∫ r : (ℝ × ℝ) × ℂ,
          correctedFutureField q branch a r*weakWaveTest (translatedTest T F) r :=
      (weak_pair_timeShift_left T (correctedFutureField q branch a) F hF).symm
    _ = ∫ r : (ℝ × ℝ) × ℂ, originalForcingDensity q branch a r*translatedTest T F r := by
      exact hbase
    _ = ∫ r : (ℝ × ℝ) × ℂ, originalForcingDensity q branch a (r + ((T,0),0))*F r :=
      source_pair_timeShift_right T (originalForcingDensity q branch a) F

/-- The literal fixed-onset full-field transgression as an exact difference of
weak pairings.  `originalForcingDensity_translation` identifies its pointwise
source difference with `onsetDefectForcingDensity`. -/
theorem complete_original_weak_wave_onset_transgression (q : XiZeroCopy)
    (branch : Bool) (a : ℂ) (T : ℝ) (F : (ℝ × ℝ) × ℂ → ℂ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hphysical : tsupport F ⊆ {r : (ℝ × ℝ) × ℂ | r.1.2 < 0}) :
    (∫ r : (ℝ × ℝ) × ℂ,
      correctedFutureField q branch a (r + ((T,0),0))*weakWaveTest F r) -
      sourceFactor q branch T*(∫ r : (ℝ × ℝ) × ℂ,
        correctedFutureField q branch a r*weakWaveTest F r) =
    (∫ r : (ℝ × ℝ) × ℂ,
      originalForcingDensity q branch a (r + ((T,0),0))*F r) -
      sourceFactor q branch T*(∫ r : (ℝ × ℝ) × ℂ,
        originalForcingDensity q branch a r*F r) := by
  rw [complete_original_weak_wave_timeShift q branch a T F hF hc hphysical]
  have hbase := complete_original_weak_wave q branch a F hF hc hphysical
  exact congrArg (fun z : ℂ => (∫ r : (ℝ × ℝ) × ℂ,
    originalForcingDensity q branch a (r + ((T,0),0))*F r)-sourceFactor q branch T*z) hbase

end
end RHTower.D4BMFullFieldOnsetTransgression
