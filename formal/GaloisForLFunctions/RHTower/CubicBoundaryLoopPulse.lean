import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A smooth two-orientation source loop with nonzero boundary pairing

The compactly supported real Schwartz coefficients satisfy `a²+b²=1` and `c²=b²`.
Their signed flux has exact pairing `∫ (a-1) (bc)' = 8/3`. The sign switches only on
an interval where `b=0`, so both source orientations glue smoothly without canceling the pairing.
This is the explicit scalar input to the cubic boundary-charge construction, not Xi admission.
-/

open Real Set MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section

namespace RHTower
def cubicLoopAngle (t : ℝ) : ℝ :=
  Real.pi * (Real.smoothTransition t - Real.smoothTransition (t - 2))
def cubicLoopA (t : ℝ) : ℝ := Real.cos (cubicLoopAngle t)
def cubicLoopB (t : ℝ) : ℝ := Real.sin (cubicLoopAngle t)
def cubicLoopSign (t : ℝ) : ℝ := 1 - 2 * Real.smoothTransition (t - 1)
def cubicLoopC (t : ℝ) : ℝ := cubicLoopSign t * cubicLoopB t
def cubicLoopFlux (t : ℝ) : ℝ := cubicLoopB t * cubicLoopC t
def cubicLoopPrimitive (t : ℝ) : ℝ :=
  cubicLoopSign t * (cubicLoopA t ^ 2 - (2 / 3 : ℝ) * cubicLoopA t ^ 3 - 1 / 3)

theorem cubicLoopAngle_smooth : ContDiff ℝ ∞ cubicLoopAngle := by
  exact contDiff_const.mul (Real.smoothTransition.contDiff.sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))
theorem cubicLoopA_smooth : ContDiff ℝ ∞ cubicLoopA :=
  cubicLoopAngle_smooth.cos
theorem cubicLoopB_smooth : ContDiff ℝ ∞ cubicLoopB :=
  cubicLoopAngle_smooth.sin
theorem cubicLoopSign_smooth : ContDiff ℝ ∞ cubicLoopSign := by
  exact contDiff_const.sub (contDiff_const.mul
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)))
theorem cubicLoopC_smooth : ContDiff ℝ ∞ cubicLoopC :=
  cubicLoopSign_smooth.mul cubicLoopB_smooth
theorem cubicLoopFlux_smooth : ContDiff ℝ ∞ cubicLoopFlux :=
  cubicLoopB_smooth.mul cubicLoopC_smooth
theorem cubicLoopPrimitive_smooth : ContDiff ℝ ∞ cubicLoopPrimitive := by
  exact cubicLoopSign_smooth.mul (((cubicLoopA_smooth.pow 2).sub
    (contDiff_const.mul (cubicLoopA_smooth.pow 3))).sub contDiff_const)

theorem cubicLoopAngle_left {t : ℝ} (ht : t ≤ 0) : cubicLoopAngle t = 0 := by
  simp [cubicLoopAngle, Real.smoothTransition.zero_of_nonpos ht,
    Real.smoothTransition.zero_of_nonpos (show t - 2 ≤ 0 by linarith)]
theorem cubicLoopAngle_right {t : ℝ} (ht : 3 ≤ t) : cubicLoopAngle t = 0 := by
  simp [cubicLoopAngle, Real.smoothTransition.one_of_one_le (show 1 ≤ t by linarith),
    Real.smoothTransition.one_of_one_le (show 1 ≤ t - 2 by linarith)]
theorem cubicLoopAngle_middle {t : ℝ} (ht : t ∈ Icc 1 2) : cubicLoopAngle t = Real.pi := by
  simp [cubicLoopAngle, Real.smoothTransition.one_of_one_le ht.1,
    Real.smoothTransition.zero_of_nonpos (show t - 2 ≤ 0 by linarith [ht.2])]
theorem cubicLoopSign_left {t : ℝ} (ht : t ≤ 1) : cubicLoopSign t = 1 := by
  simp [cubicLoopSign, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht)]
theorem cubicLoopSign_right {t : ℝ} (ht : 2 ≤ t) : cubicLoopSign t = -1 := by
  simp only [cubicLoopSign, Real.smoothTransition.one_of_one_le (show 1 ≤ t - 1 by linarith)]
  ring

theorem cubicLoop_circle (t : ℝ) : cubicLoopA t ^ 2 + cubicLoopB t ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq _

theorem cubicLoopC_sq (t : ℝ) : cubicLoopC t ^ 2 = cubicLoopB t ^ 2 := by
  by_cases h1 : t ≤ 1
  · simp [cubicLoopC, cubicLoopSign_left h1]
  by_cases h2 : 2 ≤ t
  · simp [cubicLoopC, cubicLoopSign_right h2]
  have hm : cubicLoopAngle t = Real.pi :=
    cubicLoopAngle_middle ⟨le_of_not_ge h1, le_of_not_ge h2⟩
  simp [cubicLoopC, cubicLoopB, hm]

theorem cubicLoopSign_deriv_annihilator (t : ℝ) :
    deriv cubicLoopSign t * (cubicLoopA t + 1) = 0 := by
  by_cases h1 : t < 1
  · have hd : HasDerivAt cubicLoopSign 0 t := by
      apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [gt_mem_nhds h1] with y hy
      exact cubicLoopSign_left hy.le
    rw [hd.deriv, zero_mul]
  by_cases h2 : 2 < t
  · have hd : HasDerivAt cubicLoopSign 0 t := by
      apply (hasDerivAt_const t (-1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [lt_mem_nhds h2] with y hy
      exact cubicLoopSign_right hy.le
    rw [hd.deriv, zero_mul]
  have hm := cubicLoopAngle_middle ⟨le_of_not_gt h1, le_of_not_gt h2⟩
  simp [cubicLoopA, hm]

theorem cubicLoopA_hasDerivAt (t : ℝ) :
    HasDerivAt cubicLoopA (-cubicLoopB t * deriv cubicLoopAngle t) t := by
  exact (cubicLoopAngle_smooth.differentiable (by simp) t).hasDerivAt.cos
theorem cubicLoopB_hasDerivAt (t : ℝ) :
    HasDerivAt cubicLoopB (cubicLoopA t * deriv cubicLoopAngle t) t := by
  exact (cubicLoopAngle_smooth.differentiable (by simp) t).hasDerivAt.sin

theorem cubicLoopFlux_deriv (t : ℝ) :
    deriv cubicLoopFlux t = deriv cubicLoopSign t * cubicLoopB t ^ 2 +
      2 * cubicLoopSign t * cubicLoopB t * cubicLoopA t * deriv cubicLoopAngle t := by
  have hs := (cubicLoopSign_smooth.differentiable (by simp) t).hasDerivAt
  have hb := cubicLoopB_hasDerivAt t
  have h := hb.mul (hs.mul hb)
  change HasDerivAt cubicLoopFlux _ t at h
  rw [h.deriv]
  simp only [Pi.mul_apply]
  ring

theorem cubicLoopPrimitive_deriv (t : ℝ) :
    deriv cubicLoopPrimitive t =
      deriv cubicLoopSign t * (cubicLoopA t ^ 2 - 2 / 3 * cubicLoopA t ^ 3 - 1 / 3) +
      cubicLoopSign t * ((2 * cubicLoopA t - 2 * cubicLoopA t ^ 2) *
        (-cubicLoopB t * deriv cubicLoopAngle t)) := by
  have hs := (cubicLoopSign_smooth.differentiable (by simp) t).hasDerivAt
  have ha := cubicLoopA_hasDerivAt t
  have h := hs.mul (((ha.pow 2).sub ((ha.pow 3).const_mul (2 / 3))).sub_const (1 / 3))
  change HasDerivAt cubicLoopPrimitive _ t at h
  rw [h.deriv]
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.sub_apply, Pi.pow_apply]
  ring

theorem cubicLoop_flux_exact (t : ℝ) :
    (cubicLoopA t - 1) * deriv cubicLoopFlux t =
      deriv cubicLoopPrimitive t - (4 / 3 : ℝ) * deriv cubicLoopSign t := by
  rw [cubicLoopFlux_deriv, cubicLoopPrimitive_deriv]
  have hc := cubicLoop_circle t
  have hb : cubicLoopB t ^ 2 = 1 - cubicLoopA t ^ 2 := by linarith
  rw [hb]
  have hz := cubicLoopSign_deriv_annihilator t
  linear_combination -(cubicLoopA t - 2) * (cubicLoopA t + 1) / 3 * hz

theorem cubicLoopA_sub_one_compact : HasCompactSupport (fun t => cubicLoopA t - 1) := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 3) isCompact_Icc
  intro t ht
  have ht' : t < 0 ∨ 3 < t := by
    by_cases h : t < 0
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge (fun h' => ht ⟨le_of_not_gt h, h'⟩))
  rcases ht' with ht' | ht'
  · simp [cubicLoopA, cubicLoopAngle_left ht'.le]
  · simp [cubicLoopA, cubicLoopAngle_right ht'.le]
theorem cubicLoopB_compact : HasCompactSupport cubicLoopB := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) 3) isCompact_Icc
  intro t ht
  have ht' : t < 0 ∨ 3 < t := by
    by_cases h : t < 0
    · exact Or.inl h
    · exact Or.inr (lt_of_not_ge (fun h' => ht ⟨le_of_not_gt h, h'⟩))
  rcases ht' with ht' | ht'
  · simp [cubicLoopB, cubicLoopAngle_left ht'.le]
  · simp [cubicLoopB, cubicLoopAngle_right ht'.le]
theorem cubicLoopC_compact : HasCompactSupport cubicLoopC :=
  cubicLoopB_compact.mul_left
theorem cubicLoopFlux_compact : HasCompactSupport cubicLoopFlux :=
  cubicLoopB_compact.mul_right

theorem integral_cubicLoop_flux :
    (∫ t : ℝ, (cubicLoopA t - 1) * deriv cubicLoopFlux t) = 8 / 3 := by
  have hsupp : Function.support (fun t => (cubicLoopA t - 1) * deriv cubicLoopFlux t) ⊆
      Ioc 0 3 := by
    intro t ht
    by_contra h
    have hh : t ≤ 0 ∨ 3 < t := by
      by_cases h' : t ≤ 0
      · exact Or.inl h'
      · exact Or.inr (lt_of_not_ge (fun h'' => h ⟨lt_of_not_ge h', h''⟩))
    apply ht
    rcases hh with hh | hh
    · simp [cubicLoopA, cubicLoopAngle_left hh]
    · simp [cubicLoopA, cubicLoopAngle_right hh.le]
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  have hp := cubicLoopPrimitive_smooth.continuous_deriv (by simp)
  have hs := cubicLoopSign_smooth.continuous_deriv (by simp)
  simp_rw [cubicLoop_flux_exact]
  rw [intervalIntegral.integral_sub (hp.intervalIntegrable _ _)
    ((hs.const_mul (4 / 3 : ℝ)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => cubicLoopPrimitive_smooth.differentiable (by simp) x) (hp.intervalIntegrable _ _),
    intervalIntegral.integral_deriv_eq_sub
    (fun x _ => cubicLoopSign_smooth.differentiable (by simp) x) (hs.intervalIntegrable _ _)]
  rw [cubicLoopPrimitive, cubicLoopPrimitive]
  simp only [cubicLoopA, cubicLoopAngle_left (le_refl 0),
    cubicLoopAngle_right (le_refl 3), Real.cos_zero,
    cubicLoopSign_left (show (0 : ℝ) ≤ 1 by norm_num),
    cubicLoopSign_right (show (2 : ℝ) ≤ 3 by norm_num)]
  ring

def cubicLoopFSchwartz : SchwartzMap ℝ ℂ :=
  (cubicLoopA_sub_one_compact.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (cubicLoopA_smooth.sub contDiff_const))
def cubicLoopBSchwartz : SchwartzMap ℝ ℂ :=
  (cubicLoopB_compact.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp cubicLoopB_smooth)
def cubicLoopCSchwartz : SchwartzMap ℝ ℂ :=
  (cubicLoopC_compact.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp cubicLoopC_smooth)
def cubicLoopGSchwartz : SchwartzMap ℝ ℂ :=
  (cubicLoopFlux_compact.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp cubicLoopFlux_smooth)

@[simp] theorem cubicLoopFSchwartz_apply (t : ℝ) :
    cubicLoopFSchwartz t = ((cubicLoopA t - 1 : ℝ) : ℂ) := rfl
@[simp] theorem cubicLoopBSchwartz_apply (t : ℝ) :
    cubicLoopBSchwartz t = (cubicLoopB t : ℂ) := rfl
@[simp] theorem cubicLoopCSchwartz_apply (t : ℝ) :
    cubicLoopCSchwartz t = (cubicLoopC t : ℂ) := rfl
@[simp] theorem cubicLoopGSchwartz_apply (t : ℝ) :
    cubicLoopGSchwartz t = (cubicLoopFlux t : ℂ) := rfl

theorem cubicLoopGSchwartz_deriv (t : ℝ) :
    deriv (cubicLoopGSchwartz : ℝ → ℂ) t = ((deriv cubicLoopFlux t : ℝ) : ℂ) := by
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    (cubicLoopFlux_smooth.differentiable (by simp) t).hasDerivAt).deriv

theorem integral_cubicLoop_Schwartz_pairing :
    (∫ t : ℝ, cubicLoopFSchwartz t * deriv (cubicLoopGSchwartz : ℝ → ℂ) t) =
      (8 / 3 : ℂ) := by
  simp_rw [cubicLoopFSchwartz_apply, cubicLoopGSchwartz_deriv, ← Complex.ofReal_mul]
  rw [integral_complex_ofReal, integral_cubicLoop_flux]
  simp

end RHTower

