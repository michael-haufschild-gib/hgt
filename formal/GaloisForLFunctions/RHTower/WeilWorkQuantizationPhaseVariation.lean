import GaloisForLFunctions.RHTower.WeilWorkQuantizationCumulativePhase
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Intrinsic variation of the canonical reflection phase

The actual unit-circle path has locally finite metric variation. Its cumulative
variation supplies global Lipschitz profiles without atomicity or a continuous
critical edge. These are the classical prerequisites for the source obstruction.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral

theorem lipschitzWith_circlePhase (β : ℝ) :
    LipschitzWith ⟨|β|, abs_nonneg β⟩
      (fun x : ℝ => Complex.exp (((β * x : ℝ) : ℂ) * I)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, Real.dist_eq]
  change _ ≤ |β| * |x-y|
  have heq : Complex.exp (((β*x : ℝ) : ℂ)*I) - Complex.exp (((β*y : ℝ) : ℂ)*I) =
      Complex.exp (((β*y : ℝ) : ℂ)*I) *
        (Complex.exp (I * ((β*(x-y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs, abs_mul] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := β*(x-y)))

/-- The actual unit-circle phase, with integer turns already invisible. -/
def quantizationCirclePhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I)

theorem norm_quantizationCirclePhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (x : ℝ) :
    ‖quantizationCirclePhase hW x‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem locallyBoundedVariation_quantizationCirclePhase {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) : LocallyBoundedVariationOn (quantizationCirclePhase hW) univ :=
  (lipschitzWith_circlePhase (2 * Real.pi)).comp_locallyBoundedVariationOn
    ((monotone_quantizationResidualCumulative hW).monotoneOn univ).locallyBoundedVariationOn

/-- Metric variation of the actual phase; for nonnegative x this is variation on [0,x]. -/
def quantizationPhaseVariation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (x : ℝ) : ℝ :=
  variationOnFromTo (quantizationCirclePhase hW) univ 0 x

theorem monotone_quantizationPhaseVariation {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Monotone (quantizationPhaseVariation hW) := by
  intro x y hxy
  exact variationOnFromTo.monotoneOn (locallyBoundedVariation_quantizationCirclePhase hW)
    (mem_univ 0) (mem_univ x) (mem_univ y) hxy

theorem quantizationPhaseVariation_nonneg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ quantizationPhaseVariation hW x :=
  variationOnFromTo.nonneg_of_le _ _ hx

/-- Variation is a metric clock, including jumps and flat portions. -/
theorem dist_le_dist_variationClock {f : ℝ → ℂ} (hf : LocallyBoundedVariationOn f univ)
    (x y : ℝ) : dist (f x) (f y) ≤
      dist (variationOnFromTo f univ 0 x) (variationOnFromTo f univ 0 y) := by
  have hmono : Monotone (variationOnFromTo f univ 0) := by
    intro a b hab
    exact variationOnFromTo.monotoneOn hf (mem_univ 0) (mem_univ a) (mem_univ b) hab
  have hle : ∀ a b : ℝ, a ≤ b → dist (f a) (f b) ≤
      variationOnFromTo f univ 0 b - variationOnFromTo f univ 0 a := by
    intro a b hab
    rw [variationOnFromTo.sub_right hf (mem_univ 0) (mem_univ b) (mem_univ a),
      variationOnFromTo.eq_of_le _ _ hab]
    exact (hf a b (mem_univ a) (mem_univ b)).dist_le
      ⟨mem_univ a, le_rfl, hab⟩ ⟨mem_univ b, hab, le_rfl⟩
  rcases le_total x y with hxy | hyx
  · rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hmono hxy))]
    simpa only [neg_sub] using hle x y hxy
  · rw [dist_comm (f x), Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hmono hyx))]
    exact hle y x hyx

/-- A real function controlled by a scalar clock has a global 1-Lipschitz profile. -/
theorem exists_lipschitz_clock_profile {f V : ℝ → ℝ}
    (h : ∀ x y, dist (f x) (f y) ≤ dist (V x) (V y)) :
    ∃ g : ℝ → ℝ, LipschitzWith 1 g ∧ ∀ x, g (V x) = f x := by
  let g₀ : ℝ → ℝ := fun v => f (Function.invFun V v)
  have h₀ : LipschitzOnWith 1 g₀ (range V) := by
    apply LipschitzOnWith.mk_one
    intro a ha b hb
    have hab := h (Function.invFun V a) (Function.invFun V b)
    rwa [Function.invFun_eq ha, Function.invFun_eq hb] at hab
  obtain ⟨g, hg, heq⟩ := h₀.extend_real
  refine ⟨g, hg, fun x => ?_⟩
  rw [← heq (mem_range_self x)]
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have hx := h (Function.invFun V (V x)) x
  simpa only [Function.apply_invFun_apply, dist_self, g₀] using hx

/-- No atom enumeration or differentiability of the source phase is needed. -/
theorem exists_quantization_phase_profiles {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ a b : ℝ → ℝ, LipschitzWith 1 a ∧ LipschitzWith 1 b ∧ ∀ x,
      (a (quantizationPhaseVariation hW x) : ℂ) +
        (b (quantizationPhaseVariation hW x) : ℂ) * I = quantizationCirclePhase hW x := by
  have hd := dist_le_dist_variationClock (locallyBoundedVariation_quantizationCirclePhase hW)
  obtain ⟨a, ha, hae⟩ := exists_lipschitz_clock_profile (f := fun x => (quantizationCirclePhase hW x).re)
    (V := quantizationPhaseVariation hW) (fun x y => by
      have h := Complex.abs_re_le_norm (quantizationCirclePhase hW x - quantizationCirclePhase hW y)
      rw [Complex.sub_re] at h
      exact h.trans (by simpa only [dist_eq_norm, quantizationPhaseVariation] using hd x y))
  obtain ⟨b, hb, hbe⟩ := exists_lipschitz_clock_profile (f := fun x => (quantizationCirclePhase hW x).im)
    (V := quantizationPhaseVariation hW) (fun x y => by
      have h := Complex.abs_im_le_norm (quantizationCirclePhase hW x - quantizationCirclePhase hW y)
      rw [Complex.sub_im] at h
      exact h.trans (by simpa only [dist_eq_norm, quantizationPhaseVariation] using hd x y))
  refine ⟨a,b,ha,hb,fun x => ?_⟩
  rw [hae,hbe]
  exact Complex.re_add_im _

def quantizationClockProfile (a b : ℝ → ℝ) (v : ℝ) : ℂ := (a v : ℂ) + (b v : ℂ) * I

def quantizationClockDensity (a b : ℝ → ℝ) (v : ℝ) : ℂ :=
  ((deriv a v : ℝ) : ℂ) + ((deriv b v : ℝ) : ℂ) * I

theorem continuous_quantizationClockProfile {a b : ℝ → ℝ}
    (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b) :
    Continuous (quantizationClockProfile a b) :=
  (Complex.continuous_ofReal.comp ha.continuous).add
    ((Complex.continuous_ofReal.comp hb.continuous).mul_const _)

theorem measurable_quantizationClockDensity (a b : ℝ → ℝ) :
    Measurable (quantizationClockDensity a b) :=
  (Complex.measurable_ofReal.comp (measurable_deriv _)).add
    ((Complex.measurable_ofReal.comp (measurable_deriv _)).mul_const _)

theorem norm_quantizationClockDensity_le {a b : ℝ → ℝ}
    (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b) (v : ℝ) :
    ‖quantizationClockDensity a b v‖ ≤ 2 := by
  have h1 := norm_deriv_le_of_lipschitz (x₀ := v) ha
  have h2 := norm_deriv_le_of_lipschitz (x₀ := v) hb
  simp only [NNReal.coe_one] at h1 h2
  unfold quantizationClockDensity
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real]
  linarith

theorem intervalIntegrable_clock_deriv {a : ℝ → ℝ} (ha : LipschitzWith 1 a) (u v : ℝ) :
    IntervalIntegrable (deriv a) volume u v :=
  (continuous_const.intervalIntegrable (μ := volume) u v).mono_fun'
    (measurable_deriv a).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_deriv_le_of_lipschitz (x₀ := x) ha)

/-- Classical Lipschitz FTC supplies the profile without differentiating the source phase. -/
theorem quantizationClockProfile_eq_add_integral {a b : ℝ → ℝ}
    (ha : LipschitzWith 1 a) (hb : LipschitzWith 1 b) {u v : ℝ} (huv : u ≤ v) :
    quantizationClockProfile a b v = quantizationClockProfile a b u +
      ∫ x in Ioi u, (if x ≤ v then quantizationClockDensity a b x else 0) := by
  have fa := (ha.lipschitzOnWith (s := uIcc u v)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have fb := (hb.lipschitzOnWith (s := uIcc u v)).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hset : ∫ x in Ioi u, (if x ≤ v then quantizationClockDensity a b x else 0) =
      ∫ x in u..v, quantizationClockDensity a b x := by
    rw [intervalIntegral.integral_of_le huv]
    have he : (fun x => if x ≤ v then quantizationClockDensity a b x else 0) =
        (Iic v).indicator (quantizationClockDensity a b) := by
      funext x
      simp [Set.indicator_apply]
    rw [he, setIntegral_indicator measurableSet_Iic]
    congr 1
  rw [hset]
  have haI := intervalIntegrable_clock_deriv ha u v
  have hbI := intervalIntegrable_clock_deriv hb u v
  have haI' : IntervalIntegrable (fun x => ((deriv a x : ℝ) : ℂ)) volume u v :=
    ⟨haI.1.ofReal, haI.2.ofReal⟩
  have hbI' : IntervalIntegrable (fun x => ((deriv b x : ℝ) : ℂ)) volume u v :=
    ⟨hbI.1.ofReal, hbI.2.ofReal⟩
  simp only [quantizationClockDensity]
  rw [intervalIntegral.integral_add haI' (hbI'.mul_const _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, fa, fb]
  unfold quantizationClockProfile
  push_cast
  ring

end RHTower.WeilSpectral
