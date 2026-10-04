import GaloisForLFunctions.RHTower.RoutePNativeMixedLaplaceAdmission
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Ordinary Laplace terms for the corrected native primitive

The indicator retains the physical initial clock. Holomorphy follows
from the admitted native terms, without asserting absolute admission of
the original source on an unproved half-plane.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.NativeMixedLaplace

def tail (f : ℝ → ℝ) (a : ℝ) : ℂ → ℂ :=
  bochnerLaplaceRay ((Ioi a).indicator (fun t => (f t : ℂ)))

private theorem indicator_kernel (f : ℝ → ℝ) (a : ℝ) (w : ℂ) :
    (fun t => expRay w t • (Ioi a).indicator (fun s => (f s : ℂ)) t) =
      (Ioi a).indicator (fun t => expRay w t * (f t : ℂ)) := by
  classical
  funext t
  by_cases ht : t ∈ Ioi a <;> simp [ht, smul_eq_mul]

theorem tail_eq_integral (f : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) (w : ℂ) :
    tail f a w = ∫ t in Ioi a, expRay w t * (f t : ℂ) := by
  unfold tail bochnerLaplaceRay
  rw [indicator_kernel, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi ha)]

theorem complex_admission {a : ℝ} {f : ℝ → ℝ} (w : ℂ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hi : IntegrableOn (fun t => Real.exp (-w.re * t) * f t) (Ioi a)) :
    IntegrableOn (fun t => expRay w t * (f t : ℂ)) (Ioi a) := by
  apply hi.norm.mono'
  · exact (continuous_expRay w).aestronglyMeasurable.restrict.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf)
  · filter_upwards [] with t
    simp only [norm_mul, norm_expRay, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), neg_mul]
    exact le_rfl

/-- Every open half-plane supplied by the strict real admissions is
holomorphic for the ordinary native tail transform. -/
theorem tail_analytic {a b : ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi a)))
    (hi : ∀ c : ℝ, b < c →
      IntegrableOn (fun t => Real.exp (-c * t) * f t) (Ioi a)) :
    AnalyticOnNhd ℂ (tail f a) {w : ℂ | b < w.re} := by
  have hm : AEStronglyMeasurable ((Ioi a).indicator (fun t => (f t : ℂ))) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioi).mpr
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf)
  have hd : DifferentiableOn ℂ (tail f a) {w : ℂ | b < w.re} := by
    intro w hw
    change b < w.re at hw
    let c : ℝ := (b + w.re) / 2
    have hbc : b < c := by dsimp only [c]; linarith [hw]
    have hcw : c < w.re := by dsimp only [c]; linarith [hw]
    have hr := complex_admission (c : ℂ) hf (by simpa only [Complex.ofReal_re] using hi c hbc)
    have hc : IntegrableOn (fun t => expRay (c : ℂ) t •
        (Ioi a).indicator (fun s => (f s : ℂ)) t) (Ioi 0) := by
      rw [indicator_kernel]
      have hglobal : Integrable ((Ioi a).indicator
          (fun t => expRay (c : ℂ) t * (f t : ℂ))) volume :=
        (integrable_indicator_iff measurableSet_Ioi).mpr hr
      exact hglobal.integrableOn
    exact (bochnerLaplaceRay_differentiableAt hm hc w hcw).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem complex_terminal {f : ℝ → ℝ} (w : ℂ)
    (hf : Tendsto (fun t => Real.exp (-w.re * t) * f t) atTop (𝓝 0)) :
    Tendsto (fun t => expRay w t * (f t : ℂ)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at hf ⊢
  have heq : (fun t => ‖expRay w t * (f t : ℂ)‖) =
      (fun t => ‖Real.exp (-w.re * t) * f t‖) := by
    funext t
    simp only [norm_mul, norm_expRay, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), neg_mul]
  rw [heq]
  exact hf

/-- The actual corrected primitive and reciprocal density yield
holomorphic tail terms and a vanishing complex terminal term under the
signed-growth contradiction hypothesis. -/
theorem exists_nativeTailHolomorphy :
    ∃ T : ℝ, 0 < T ∧ ∀ ε b a C : ℝ, T < a → 0 ≤ b → 0 ≤ C →
      (∀ t : ℝ, a < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t)) →
      AnalyticOnNhd ℂ (tail (routePNativeMixedCorrectedPrimitive ε) a) {w : ℂ | b < w.re} ∧
      AnalyticOnNhd ℂ (tail (density ε) a) {w : ℂ | b < w.re} ∧
      ∀ w : ℂ, b < w.re →
        Tendsto (fun t => expRay w t * (routePNativeMixedCorrectedPrimitive ε t : ℂ))
          atTop (𝓝 0) := by
  obtain ⟨Tg, hTg, hg⟩ := exists_growthTransfer
  obtain ⟨Tc, _, hc⟩ := exists_routePNativeMixedCorrectedPrimitiveCalculus
  refine ⟨max Tg Tc, hTg.trans_le (le_max_left _ _), ?_⟩
  intro ε b a C hTa hb hC hQ
  have hga : Tg < a := (le_max_left _ _).trans_lt hTa
  have hca : Tc < a := (le_max_right _ _).trans_lt hTa
  have ha : 0 < a := hTg.trans hga
  have hP := ((hc ε).1.mono (Ioi_subset_Ioi hca.le)).aestronglyMeasurable
    (μ := volume) measurableSet_Ioi
  have hQcont : ContinuousOn (routePNativeLatePrimeMixedPrimitive ε) (Ioi a) := by
    intro t ht
    exact (continuousAt_routePNativeLatePrimeMixedPrimitive ε (ha.trans ht)).continuousWithinAt
  have hD : AEStronglyMeasurable (density ε) (volume.restrict (Ioi a)) :=
    (hQcont.aestronglyMeasurable measurableSet_Ioi).mul
      (measurable_routePLatePrimeVelocity.div
        (measurable_routePLatePrimeIncrement.pow_const 2)).aestronglyMeasurable.restrict
  have hi := hg ε b a C hga.le hb hC hQ
  refine ⟨tail_analytic hP (fun c hc => (hi c hc).1),
    tail_analytic hD (fun c hc => (hi c hc).2.1), ?_⟩
  intro w hw
  exact complex_terminal w (hi w.re hw).2.2

end RHTower.NativeMixedLaplace
