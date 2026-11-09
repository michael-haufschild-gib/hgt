import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSquaredSignedLaplaceNoGo
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Local recovery of the Gaussian rate measure

The first Laplace moment of a finite causal measure determines its restriction
to positive rates from any open interval. No moment assumption is needed:
exponential tilting makes the observed moment a finite measure. Its weight
vanishes only at zero, the scalar term annihilated by the Gaussian operator.
The statement includes infinitely many atoms and continuous singular sources.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal NNReal

namespace GaloisForLFunctions.EulerFETransportTheory

noncomputable section

/-- Local real Laplace data determine an entire finite causal measure. -/
theorem finiteMeasure_eq_of_laplace_local {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b,
      (∫ u, Real.exp (-x * u) ∂μ) = ∫ u, Real.exp (-x * u) ∂ν) : μ = ν := by
  have han : AnalyticOnNhd ℂ
      (fun z => _root_.RHTower.finiteComplexLaplace μ z -
        _root_.RHTower.finiteComplexLaplace ν z) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hopen := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    have hm := _root_.RHTower.differentiableOn_finiteComplexLaplace_openRightHalfPlane μ hμ
    have hn := _root_.RHTower.differentiableOn_finiteComplexLaplace_openRightHalfPlane ν hν
    exact (hm.analyticAt hopen).sub (hn.analyticAt hopen)
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by dsimp [c]; constructor <;> linarith
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] c,
      _root_.RHTower.finiteComplexLaplace μ x -
        _root_.RHTower.finiteComplexLaplace ν x = 0 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Ioo_mem_nhds hc.1 hc.2)] with x hx
    rw [_root_.RHTower.finiteComplexLaplace_ofReal,
      _root_.RHTower.finiteComplexLaplace_ofReal,
      integral_complex_ofReal, integral_complex_ofReal, heq x hx, sub_self]
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] c) (𝓝[≠] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(Complex.continuous_ofReal.tendsto c).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using hx
  have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected
    (show 0 < (c : ℂ).re from ha.trans hc.1) (ht.frequently hev.frequently)
  apply HTGeometry.measure_eq_of_laplace_eq hμ hν
  intro x hx
  have he := sub_eq_zero.1 (hall (show 0 < (x : ℂ).re from hx))
  simpa only [_root_.RHTower.finiteComplexLaplace_ofReal,
    integral_complex_ofReal, Complex.ofReal_inj] using he

/-- First rate moment, the data retained by the Gaussian differential defect. -/
def gaussianMeasureMoment (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ u, u * Real.exp (-x * u) ∂μ

/-- The full Laplace response retains the mass at zero as a constant. -/
def gaussianMeasureLaplace (μ : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ u, Real.exp (-x * u) ∂μ

theorem integrable_gaussianMeasureLaplace (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun u => Real.exp (-x * u)) μ := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards [ae_iff.2 hμ] with u hu
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hx hu])

/-- A finite causal measure needs no undamped first moment to differentiate. -/
theorem hasDerivAt_gaussianMeasureLaplace (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianMeasureLaplace μ) (-gaussianMeasureMoment μ x) x := by
  let c := x / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hd : Integrable (fun u => -(u * Real.exp (-x * u))) μ ∧
      HasDerivAt (gaussianMeasureLaplace μ)
        (∫ u, -(u * Real.exp (-x * u)) ∂μ) x :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := fun y u => Real.exp (-y * u))
      (F' := fun y u => -(u * Real.exp (-y * u)))
      (bound := fun _ => c⁻¹) (x₀ := x)
      (Ioi_mem_nhds (show c < x by dsimp [c]; linarith))
      (Eventually.of_forall fun _ => by fun_prop)
      (integrable_gaussianMeasureLaplace μ hμ hx.le) (by fun_prop) ?_
      (integrable_const _) ?_
  · simpa only [gaussianMeasureMoment, integral_neg] using hd.2
  · filter_upwards [ae_iff.2 hμ] with u hu y hy
    rw [norm_neg, Real.norm_of_nonneg (mul_nonneg hu (Real.exp_pos _).le)]
    calc u * Real.exp (-y * u) ≤ u * Real.exp (-c * u) := by
          gcongr
          exact hy.le
      _ ≤ c⁻¹ := GaloisForLFunctions.RHTower.mul_exp_neg_le hc
  · exact Eventually.of_forall fun u y _ =>
      (((hasDerivAt_id y).neg.mul_const u).exp).congr_deriv
        (by simp only [Pi.neg_apply, id]; ring)

private def momentTilt (μ : Measure ℝ) (c : ℝ) : Measure ℝ :=
  μ.withDensity (fun u => ENNReal.ofReal (u * Real.exp (-c * u)))

private theorem integrable_momentWeight (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) {c : ℝ} (hc : 0 < c) :
    Integrable (fun u => u * Real.exp (-c * u)) μ := by
  refine (integrable_const c⁻¹).mono' (by fun_prop) ?_
  filter_upwards [ae_iff.2 hμ] with u hu
  rw [Real.norm_of_nonneg (mul_nonneg hu (Real.exp_pos _).le)]
  exact GaloisForLFunctions.RHTower.mul_exp_neg_le hc

private theorem finite_momentTilt (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) {c : ℝ} (hc : 0 < c) :
    IsFiniteMeasure (momentTilt μ c) := by
  apply isFiniteMeasure_withDensity
  have hi := integrable_momentWeight μ hμ hc
  have hf : ∫⁻ u, ‖u * Real.exp (-c * u)‖ₑ ∂μ < ⊤ := hi.2
  apply ne_of_lt
  exact (lintegral_mono fun u => ENNReal.ofReal_le_ofReal (le_abs_self _)).trans_lt
    (by simpa only [Real.enorm_eq_ofReal_abs] using hf)

private theorem momentTilt_laplace (μ : Measure ℝ)
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (c x : ℝ) :
    (∫ u, Real.exp (-x * u) ∂momentTilt μ c) = gaussianMeasureMoment μ (x + c) := by
  rw [momentTilt, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_iff.2 hμ] with u hu
  rw [ENNReal.toReal_ofReal (mul_nonneg hu (Real.exp_pos _).le), smul_eq_mul,
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Equality of local differential data recovers all positive rates, including
infinite atomic and singular continuous parts. Only the mass at zero is lost. -/
theorem restrict_Ioi_eq_of_gaussianMeasureMoment_local {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ (Ici (0 : ℝ))ᶜ = 0) (hν : ν (Ici (0 : ℝ))ᶜ = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (heq : ∀ x ∈ Ioo a b, gaussianMeasureMoment μ x = gaussianMeasureMoment ν x) :
    μ.restrict (Ioi 0) = ν.restrict (Ioi 0) := by
  let c := a / 2
  have hc : 0 < c := by dsimp [c]; linarith
  letI := finite_momentTilt μ hμ hc
  letI := finite_momentTilt ν hν hc
  have ht : momentTilt μ c = momentTilt ν c := by
    apply finiteMeasure_eq_of_laplace_local (μ := momentTilt μ c) (ν := momentTilt ν c)
      (withDensity_absolutelyContinuous _ _ hμ)
      (withDensity_absolutelyContinuous _ _ hν)
      (a := a - c) (b := b - c) (by dsimp [c]; linarith) (by linarith)
    intro x hx
    rw [momentTilt_laplace μ hμ, momentTilt_laplace ν hν]
    exact heq (x + c) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  let w : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u * Real.exp (-c * u))
  have hw : Measurable w := by fun_prop
  have hrec (ρ : Measure ℝ) :
      ((momentTilt ρ c).restrict (Ioi 0)).withDensity (fun u => (w u)⁻¹) =
        ρ.restrict (Ioi 0) := by
    rw [momentTilt, restrict_withDensity measurableSet_Ioi]
    apply withDensity_inv_same hw
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact ne_of_gt (ENNReal.ofReal_pos.2 (mul_pos hu (Real.exp_pos _)))
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_ne_top
  rw [← hrec μ, ← hrec ν, ht]

#print axioms restrict_Ioi_eq_of_gaussianMeasureMoment_local

end

end GaloisForLFunctions.EulerFETransportTheory
