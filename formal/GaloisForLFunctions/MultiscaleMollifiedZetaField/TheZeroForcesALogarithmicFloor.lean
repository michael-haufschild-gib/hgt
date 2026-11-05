import GaloisForLFunctions.RHTower.ZetaCriticalLineJensenInequality
import GaloisForLFunctions.RHTower.MoebiusMollifiedZetaField
import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# A zero of `ζ` forces a logarithmic floor under every prefix-cancelling mollifier

Let `M` be entire and bounded on `Re s ≥ ½`, and suppose the Dirichlet coefficients of `E = ζM − 1` vanish up to `y`.
For a zero `ρ = ½ + δ + iγ` of `ζ` with `0 < δ < ½`,

  `∫ P_ρ(u) log |E(½ + iu)| du ≥ δ log (y + 1) − log (|ρ| / |1 − ρ|)`,   `P_ρ(u) = δ / (π (δ² + (u − γ)²))`

(`integrable_and_poisson_log_floor`). `P_ρ` is the harmonic measure of `Re z > ½` seen from `ρ`.

**Mechanism.** The disc map `w ↦ ½ − δ + iγ + 2δ/(1 − w)` carries `0` to `ρ` and the unit circle to the critical line, so boundary
Jensen on the disc becomes the half-plane inequality `log |G(ρ)| ≤ ∫ P_ρ log |G(½ + iu)| du` for entire `G` of polynomial growth
(`integrable_and_log_norm_le_poisson`). Take `G(z) = (y + 1)^{z − ½} (z − 1) E(z)`. The coefficients of `E` start after `y`, so the
exponential factor stays bounded as `Re z → ∞`; it has modulus one on the line and gains `(y + 1)^δ` at `ρ`, where `E(ρ) = −1`.
The factor `z − 1` has the modulus of `z` on the line, and the Poisson mean of `log |z|` there is exactly `log |ρ|`
(`integrable_and_integral_poisson_log_norm_line`).

Jensen's inequality for the probability measure `P_ρ` turns the floor into one at every exponent `p > 0`
(`le_integral_poisson_norm_rpow`). At `p = 2` it reads `(y + 1)^{2δ} |1 − ρ|²/|ρ|² ≤ ∫ P_ρ |E|²`.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The point `½ + δ + iγ`. -/
def offLinePoint (δ γ : ℝ) : ℂ := ((1 / 2 + δ : ℝ) : ℂ) + (γ : ℂ) * I

/-- The point `½ + iu` of the critical line. -/
def linePoint (u : ℝ) : ℂ := (1 / 2 : ℂ) + (u : ℂ) * I

theorem offLinePoint_re (δ γ : ℝ) : (offLinePoint δ γ).re = 1 / 2 + δ := by simp [offLinePoint]

theorem offLinePoint_im (δ γ : ℝ) : (offLinePoint δ γ).im = γ := by simp [offLinePoint]

theorem linePoint_re (u : ℝ) : (linePoint u).re = 1 / 2 := by simp [linePoint]

theorem linePoint_im (u : ℝ) : (linePoint u).im = u := by simp [linePoint]

theorem linePoint_ne_one (u : ℝ) : linePoint u ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  rw [linePoint_re] at this
  norm_num at this

theorem linePoint_injective : Function.Injective linePoint := fun u v h => by
  have := congrArg Complex.im h
  rwa [linePoint_im, linePoint_im] at this

theorem continuous_linePoint : Continuous linePoint := by
  unfold linePoint
  fun_prop

/-- The map from the unit disc onto `Re z > ½` sending `0` to `½ + δ + iγ`. -/
def discToPoint (δ γ : ℝ) (w : ℂ) : ℂ :=
  offLinePoint (-δ) γ + 2 * (δ : ℂ) * _root_.RHTower.halfPlaneOfDisc w

theorem discToPoint_zero (δ γ : ℝ) : discToPoint δ γ 0 = offLinePoint δ γ := by
  simp only [discToPoint, offLinePoint, _root_.RHTower.halfPlaneOfDisc, sub_zero, inv_one]
  push_cast
  ring

theorem discToPoint_circleMap (δ γ t : ℝ) :
    discToPoint δ γ (circleMap 0 1 (_root_.RHTower.criticalLineAngle t)) =
      linePoint (γ + 2 * δ * t) := by
  simp only [discToPoint, _root_.RHTower.halfPlaneOfDisc_circleMap_criticalLineAngle, offLinePoint,
    linePoint]
  push_cast
  ring

theorem re_discToPoint_ge {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    1 / 2 ≤ (discToPoint δ γ w).re := by
  have hh := _root_.RHTower.re_halfPlaneOfDisc_ge hw hw1
  have hre : (discToPoint δ γ w).re =
      1 / 2 + -δ + 2 * δ * (_root_.RHTower.halfPlaneOfDisc w).re := by
    simp [discToPoint, offLinePoint, Complex.mul_re]
  rw [hre]
  nlinarith

theorem differentiableAt_discToPoint (δ γ : ℝ) {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ (discToPoint δ γ) w := by
  have hw1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  unfold discToPoint _root_.RHTower.halfPlaneOfDisc
  exact (differentiableAt_const _).add
    (((differentiableAt_const _).sub differentiableAt_id).inv hw1 |>.const_mul _)

theorem measurable_discToPoint (δ γ : ℝ) : Measurable (discToPoint δ γ) := by
  unfold discToPoint _root_.RHTower.halfPlaneOfDisc
  exact measurable_const.add (measurable_const.mul (measurable_const.sub measurable_id).inv)

/-- The Poisson density in the variable `t` of the disc parametrization. -/
private theorem halfPlanePoisson_mul_eq {δ : ℝ} (hδ : 0 < δ) (t x : ℝ) :
    x / (1 / 4 + t ^ 2) = 4 * Real.pi * δ * (halfPlanePoisson δ (2 * δ * t) * x) := by
  have hπ := Real.pi_pos
  have h : 0 < 1 / 4 + t ^ 2 := by positivity
  have hden : δ ^ 2 + (2 * δ * t) ^ 2 = 4 * δ ^ 2 * (1 / 4 + t ^ 2) := by ring
  rw [halfPlanePoisson, hden]
  field_simp

/-- **The circle average is the Poisson mean on the critical line.** -/
theorem circleAverage_discToPoint_eq {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) (g : ℂ → ℝ) :
    Real.circleAverage (fun w => g (discToPoint δ γ w)) 0 1 =
      ∫ u : ℝ, halfPlanePoisson δ (u - γ) * g (linePoint u) := by
  set f : ℝ → ℝ := fun u => halfPlanePoisson δ (u - γ) * g (linePoint u) with hf
  have hc : (2 * δ) ≠ 0 := by positivity
  have hline : ∀ t : ℝ,
      g (discToPoint δ γ (circleMap 0 1 (_root_.RHTower.criticalLineAngle t))) / (1 / 4 + t ^ 2) =
        4 * Real.pi * δ * f (γ + 2 * δ * t) := by
    intro t
    rw [discToPoint_circleMap, halfPlanePoisson_mul_eq hδ]
    simp only [hf, add_sub_cancel_left]
  rw [_root_.RHTower.circleAverage_eq_integral_criticalLine]
  simp only [hline]
  rw [integral_const_mul]
  have hsub : (∫ t : ℝ, f (γ + 2 * δ * t)) = (2 * δ)⁻¹ * ∫ u : ℝ, f u := by
    have h1 := Measure.integral_comp_mul_left (fun s : ℝ => f (γ + s)) (2 * δ)
    rw [h1, integral_add_left_eq_self, smul_eq_mul]
    congr 1
    rw [abs_inv, abs_of_pos (by positivity)]
  rw [hsub]
  have hπ := Real.pi_pos
  field_simp
  ring

/-- Circle integrability transfers to the Poisson integrand on the critical line. -/
theorem integrable_poisson_of_circleIntegrable {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) {g : ℂ → ℝ}
    (hci : CircleIntegrable (fun w => g (discToPoint δ γ w)) 0 1) :
    Integrable fun u : ℝ => halfPlanePoisson δ (u - γ) * g (linePoint u) := by
  set f : ℝ → ℝ := fun u => halfPlanePoisson δ (u - γ) * g (linePoint u) with hf
  have hc : (2 * δ) ≠ 0 := by positivity
  have hint := (_root_.RHTower.circleIntegrable_iff_integrable_criticalLine _).mp hci
  have ht : Integrable fun t : ℝ => f (γ + 2 * δ * t) := by
    have h := hint.const_mul (4 * Real.pi * δ)⁻¹
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [discToPoint_circleMap]
    rw [halfPlanePoisson_mul_eq hδ t]
    simp only [hf, add_sub_cancel_left]
    have hπ := Real.pi_pos
    field_simp
  have h1 : Integrable (fun t : ℝ => (fun s : ℝ => f (γ + s)) (2 * δ * t)) := ht
  have h2 := (integrable_comp_mul_left_iff (fun s : ℝ => f (γ + s)) hc).mp h1
  have h3 := h2.comp_add_left (-γ)
  refine h3.congr (Eventually.of_forall fun u => ?_)
  simp

/-- **Half-plane Jensen.** For `F` entire with at most quadratic growth on `Re z ≥ ½` and `F(ρ) ≠ 0`, the logarithm of `|F|` is
integrable against `P_ρ` on the critical line, and `log |F(ρ)| ≤ ∫ P_ρ log |F(½ + iu)| du`. -/
theorem integrable_and_log_norm_le_poisson {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖F z‖ ≤ C * (‖z‖ + 2) ^ 2) {δ γ : ℝ} (hδ : 0 < δ)
    (h0 : F (offLinePoint δ γ) ≠ 0) :
    Integrable (fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log ‖F (linePoint u)‖) ∧
      Real.log ‖F (offLinePoint δ γ)‖ ≤
        ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log ‖F (linePoint u)‖ := by
  set Φ : ℂ → ℂ := fun w => F (discToPoint δ γ w) with hΦ
  have hdiff : DifferentiableOn ℂ Φ {1}ᶜ := fun w hw =>
    ((hF _).comp w (differentiableAt_discToPoint δ γ hw)).differentiableWithinAt
  have hmeas : Measurable Φ := hF.continuous.measurable.comp (measurable_discToPoint δ γ)
  have hΦ0 : Φ 0 = F (offLinePoint δ γ) := by simp only [hΦ, discToPoint_zero]
  have hne0 : Φ 0 ≠ 0 := by rw [hΦ0]; exact h0
  have hgrowth : ∃ A : ℝ, ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 →
      Real.log ‖Φ w‖ ≤ A - 2 * Real.log ‖1 - w‖ := by
    set a : ℝ := ‖offLinePoint (-δ) γ‖ with ha
    set K : ℝ := 2 * (a + 2) + 2 * δ with hK
    have hK0 : 0 < K := by positivity
    refine ⟨max 0 (Real.log (max C 1 * K ^ 2)) + 2 * Real.log 2, fun w hw hw1 => ?_⟩
    have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
    have hn0 : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
    have hn2 : ‖1 - w‖ ≤ 2 := by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 2 := by rw [norm_one]; linarith
    have hh : ‖_root_.RHTower.halfPlaneOfDisc w‖ = ‖1 - w‖⁻¹ := by
      rw [_root_.RHTower.halfPlaneOfDisc, norm_inv]
    have hinv : 1 ≤ 2 * ‖1 - w‖⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hn0]
      linarith
    have hz : ‖discToPoint δ γ w‖ + 2 ≤ K * ‖1 - w‖⁻¹ := by
      have h1 : ‖discToPoint δ γ w‖ ≤ a + 2 * δ * ‖1 - w‖⁻¹ := by
        refine (norm_add_le _ _).trans ?_
        have h2 : ‖2 * (δ : ℂ) * _root_.RHTower.halfPlaneOfDisc w‖ = 2 * δ * ‖1 - w‖⁻¹ := by
          rw [norm_mul, norm_mul, hh]
          simp [abs_of_pos hδ]
        rw [h2]
      have hinv0 : 0 ≤ ‖1 - w‖⁻¹ := by positivity
      simp only [hK]
      nlinarith [norm_nonneg (offLinePoint (-δ) γ)]
    have hb := hgrow _ (re_discToPoint_ge hδ γ hw hw1)
    have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    have hsq : (‖discToPoint δ γ w‖ + 2) ^ 2 ≤ K ^ 2 * (‖1 - w‖⁻¹) ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hz 2
    have hΦb : ‖Φ w‖ ≤ max C 1 * K ^ 2 * (‖1 - w‖⁻¹) ^ 2 := by
      calc ‖Φ w‖ ≤ C * (‖discToPoint δ γ w‖ + 2) ^ 2 := hb
        _ ≤ max C 1 * (‖discToPoint δ γ w‖ + 2) ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C 1 * (K ^ 2 * (‖1 - w‖⁻¹) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = max C 1 * K ^ 2 * (‖1 - w‖⁻¹) ^ 2 := by ring
    have hlog2 : Real.log ‖1 - w‖ ≤ Real.log 2 := Real.log_le_log hn0 hn2
    have hlogsq : Real.log ((‖1 - w‖⁻¹) ^ 2) = -(2 * Real.log ‖1 - w‖) := by
      rw [Real.log_pow, Real.log_inv]
      push_cast
      ring
    have hcpos : 0 < max C 1 * K ^ 2 := by positivity
    rcases eq_or_ne (Φ w) 0 with hz0 | hz0
    · rw [hz0, norm_zero, Real.log_zero]
      have := le_max_left 0 (Real.log (max C 1 * K ^ 2))
      linarith
    · have hlog : Real.log ‖Φ w‖ ≤
          Real.log (max C 1 * K ^ 2) - 2 * Real.log ‖1 - w‖ := by
        have h1 := Real.log_le_log (norm_pos_iff.mpr hz0) hΦb
        rw [Real.log_mul hcpos.ne' (by positivity), hlogsq] at h1
        linarith
      have := le_max_right 0 (Real.log (max C 1 * K ^ 2))
      have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
  obtain ⟨hci, hineq⟩ := _root_.RHTower.circleIntegrable_and_sum_log_add_le_circleAverage hdiff
    hmeas hne0 hgrowth (U := ∅) (by simp)
  simp only [Finset.sum_empty, zero_add] at hineq
  have hg : (fun w => Real.log ‖Φ w‖) =
      fun w => (fun z => Real.log ‖F z‖) (discToPoint δ γ w) := rfl
  rw [hg] at hci hineq
  refine ⟨integrable_poisson_of_circleIntegrable (g := fun z => Real.log ‖F z‖) hδ γ hci, ?_⟩
  rw [circleAverage_discToPoint_eq hδ γ (fun z => Real.log ‖F z‖), hΦ0] at hineq
  exact hineq

/-- **The Poisson mean of `log |z|` on the critical line is `log |ρ|`.** The function `z` has no zero in `Re z > ½`. -/
theorem integrable_and_integral_poisson_log_norm_line {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (γ : ℝ) :
    Integrable (fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log ‖linePoint u‖) ∧
      ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log ‖linePoint u‖ =
        Real.log ‖offLinePoint δ γ‖ := by
  have hρ0 : offLinePoint δ γ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [offLinePoint_re] at this
    simp only [Complex.zero_re] at this
    linarith
  have hint := (integrable_and_log_norm_le_poisson (F := id) differentiable_id (C := 1)
    (fun z _ => by
      simp only [id, one_mul]
      nlinarith [norm_nonneg z]) hδ (by simpa using hρ0)).1
  refine ⟨by simpa using hint, ?_⟩
  set ρ := offLinePoint δ γ with hρ
  set a := offLinePoint (-δ) γ with ha
  have ha0 : a ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [ha, offLinePoint_re] at this
    simp only [Complex.zero_re] at this
    linarith
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hnormle : ‖a‖ < ‖ρ‖ := by
    have h1 : ‖a‖ ^ 2 < ‖ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply, ha, hρ, offLinePoint_re, offLinePoint_re, offLinePoint_im,
        offLinePoint_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1
  have hρa : ρ = a + 2 * (δ : ℂ) := by
    simp only [hρ, ha, offLinePoint]
    push_cast
    ring
  set c : ℂ := ρ / a with hc
  have hcn : 1 < ‖c‖ := by
    rw [hc, norm_div, one_lt_div hna]
    exact hnormle
  set g₁ : ℂ → ℝ := fun w =>
    Real.log ‖a‖ + (Real.log ‖w - c‖ - Real.log ‖w - 1‖) with hg₁
  have hci1 : CircleIntegrable (fun w : ℂ => Real.log ‖w - c‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (f := fun w : ℂ => w - c)
      (fun w _ => (analyticAt_id.sub analyticAt_const).meromorphicAt)
  have hci2 : CircleIntegrable (fun w : ℂ => Real.log ‖w - 1‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (f := fun w : ℂ => w - 1)
      (fun w _ => (analyticAt_id.sub analyticAt_const).meromorphicAt)
  have havg1 : Real.circleAverage g₁ 0 1 = Real.log ‖ρ‖ := by
    have hsub : Real.circleAverage (fun w : ℂ => Real.log ‖w - c‖ - Real.log ‖w - 1‖) 0 1 =
        Real.circleAverage (fun w : ℂ => Real.log ‖w - c‖) 0 1 -
          Real.circleAverage (fun w : ℂ => Real.log ‖w - 1‖) 0 1 := by
      have h := Real.circleAverage_sub hci1 hci2
      simpa [Pi.sub_def] using h
    have hadd : Real.circleAverage g₁ 0 1 = Real.log ‖a‖ +
        Real.circleAverage (fun w : ℂ => Real.log ‖w - c‖ - Real.log ‖w - 1‖) 0 1 := by
      have h := Real.circleAverage_add (circleIntegrable_const (Real.log ‖a‖) 0 1) (hci1.sub hci2)
      simp only [Pi.add_def, Real.circleAverage_const] at h
      simpa [hg₁, Pi.sub_def] using h
    have h1 : Real.circleAverage (fun w : ℂ => Real.log ‖w - c‖) 0 1 = Real.posLog ‖c‖ :=
      circleAverage_log_norm_sub_const_eq_posLog
    have h2 : Real.circleAverage (fun w : ℂ => Real.log ‖w - 1‖) 0 1 = 0 :=
      circleAverage_log_norm_sub_const₁ (by simp)
    rw [hadd, hsub, h1, h2, Real.posLog_eq_log_max_one (norm_nonneg _), max_eq_right hcn.le, hc,
      norm_div, Real.log_div (norm_pos_iff.mpr (by
        intro h0; rw [h0, norm_zero] at hnormle; linarith)).ne' hna.ne']
    ring
  have hpt : ∀ t : ℝ, g₁ (circleMap 0 1 (_root_.RHTower.criticalLineAngle t)) =
      Real.log ‖discToPoint δ γ (circleMap 0 1 (_root_.RHTower.criticalLineAngle t))‖ := by
    intro t
    set w := circleMap 0 1 (_root_.RHTower.criticalLineAngle t) with hw
    have hwn : ‖w‖ = 1 := by simp [hw]
    have hh := _root_.RHTower.halfPlaneOfDisc_circleMap_criticalLineAngle t
    have hw1 : (1 : ℂ) - w ≠ 0 := by
      intro h0
      have h1 : _root_.RHTower.halfPlaneOfDisc w = 0 := by
        rw [_root_.RHTower.halfPlaneOfDisc, h0, inv_zero]
      rw [← hw] at hh
      rw [h1] at hh
      have := congrArg Complex.re hh
      norm_num at this
    have hwne : w - 1 ≠ 0 := fun h0 => hw1 (by linear_combination -h0)
    have hwc : w - c ≠ 0 := by
      intro h0
      have : w = c := sub_eq_zero.mp h0
      rw [this] at hwn
      linarith
    have hfact : discToPoint δ γ w = -a * (w - c) / (1 - w) := by
      unfold discToPoint _root_.RHTower.halfPlaneOfDisc
      rw [← ha, hc]
      field_simp
      rw [hρa]
      ring
    have hnorm1 : ‖(1 : ℂ) - w‖ = ‖w - 1‖ := by rw [← norm_neg, neg_sub]
    rw [hfact, norm_div, norm_mul, norm_neg, hnorm1,
      Real.log_div (mul_ne_zero hna.ne' (norm_ne_zero_iff.mpr hwc)) (norm_ne_zero_iff.mpr hwne),
      Real.log_mul hna.ne' (norm_ne_zero_iff.mpr hwc)]
    simp only [hg₁]
    ring
  have hfin : Real.circleAverage (fun w => Real.log ‖discToPoint δ γ w‖) 0 1 = Real.log ‖ρ‖ := by
    rw [← havg1, _root_.RHTower.circleAverage_eq_integral_criticalLine,
      _root_.RHTower.circleAverage_eq_integral_criticalLine]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hpt]
  have h := circleAverage_discToPoint_eq hδ γ (fun z => Real.log ‖z‖)
  rw [← h]
  exact hfin

/-! ### The prefix-amplified floor -/

/-- A Dirichlet series with no coefficients up to `N` decays like `(N + 1)^{−(σ − 3)}` on `Re s = σ ≥ 3`. -/
theorem norm_LSeries_le_rpow_of_vanishing_head {c : ℕ → ℂ} {N : ℕ} (hN : 1 ≤ N) {B : ℝ}
    (hB : 0 ≤ B) (hzero : ∀ n, n ≤ N → c n = 0) (hbound : ∀ n, N < n → ‖c n‖ ≤ B * n) {s : ℂ}
    (hs : 3 ≤ s.re) :
    ‖LSeries c s‖ ≤ ((N : ℝ) + 1) ^ (3 - s.re) * (B * (2 / N)) := by
  set R : ℝ := ((N : ℝ) + 1) ^ (3 - s.re) with hR
  have hR0 : 0 < R := by positivity
  set g : ℕ → ℝ := fun n => if N < n then (((n : ℝ) ^ 2)⁻¹) else 0 with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by simp only [hg]; split_ifs <;> positivity
  have hterm : ∀ n : ℕ, ‖LSeries.term c s n‖ ≤ R * B * g n := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [if_pos h0]
      exact mul_nonneg (by positivity) (hg0 n)
    · rw [if_neg hpos.ne']
      by_cases hNn : N < n
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
        have hnN : (N : ℝ) + 1 ≤ n := by exact_mod_cast hNn
        have hc := hbound n hNn
        have hgn : g n = ((n : ℝ) ^ 2)⁻¹ := by simp only [hg, if_pos hNn]
        have hmono : (n : ℝ) ^ (3 - s.re) ≤ R :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hnN (by linarith)
        have hsplit : (n : ℝ) ^ s.re = (n : ℝ) ^ (3 : ℝ) / (n : ℝ) ^ (3 - s.re) := by
          rw [← Real.rpow_sub hn0]
          congr 1
          ring
        have hpow3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ 3 := by
          exact_mod_cast Real.rpow_natCast (n : ℝ) 3
        have hpp : 0 < (n : ℝ) ^ (3 - s.re) := by positivity
        rw [hgn, hsplit, hpow3, div_div_eq_mul_div, div_le_iff₀ (by positivity)]
        calc ‖c n‖ * (n : ℝ) ^ (3 - s.re) ≤ (B * n) * R :=
              mul_le_mul hc hmono hpp.le (by positivity)
          _ = R * B * ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ 3 := by
              field_simp
      · rw [hzero n (not_lt.mp hNn), norm_zero, zero_div]
        exact mul_nonneg (by positivity) (hg0 n)
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun n => ?_)
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    simp only [hg]
    split_ifs
    · rw [one_div]
    · positivity
  have htsum : ∑' n, g n ≤ 2 / N := by
    refine hgsum.tsum_le_of_sum_le fun S => ?_
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ S, n < M := ⟨S.sup id + 1, fun n hn =>
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
    calc ∑ n ∈ S, g n ≤ ∑ n ∈ Finset.range M, g n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_range.mpr (hM n hn))
            fun n _ _ => hg0 n
      _ = ∑ n ∈ Finset.Ioo N M, ((n : ℝ) ^ 2)⁻¹ := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range M) (fun n => N < n)]
          have h1 : ∑ n ∈ (Finset.range M).filter (fun n => ¬ N < n), g n = 0 :=
            Finset.sum_eq_zero fun n hn => by
              simp only [hg, if_neg (Finset.mem_filter.mp hn).2]
          rw [h1, add_zero]
          have hset : (Finset.range M).filter (fun n => N < n) = Finset.Ioo N M := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
            tauto
          rw [hset]
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [hg, if_pos (Finset.mem_Ioo.mp hn).1]
      _ ≤ 2 / ((N : ℝ) + 1) := sum_Ioo_inv_sq_le N M
      _ ≤ 2 / N := by
          have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
          exact div_le_div_of_nonneg_left (by norm_num) hN0 (by linarith)
  have hsumnorm : Summable fun n => ‖LSeries.term c s n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hgsum.mul_left _)
  calc ‖LSeries c s‖ ≤ ∑' n, ‖LSeries.term c s n‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n, R * B * g n := hsumnorm.tsum_le_tsum hterm (hgsum.mul_left _)
    _ = R * B * ∑' n, g n := tsum_mul_left
    _ ≤ R * B * (2 / N) := mul_le_mul_of_nonneg_left htsum (by positivity)
    _ = R * (B * (2 / N)) := by ring

/-- The function `G(z) = (y + 1)^{z − ½} ((z − 1) ζ(z) M(z) − (z − 1))`, entire of quadratic growth on `Re z ≥ ½`. -/
def prefixField (M : ℂ → ℂ) (y : ℕ) (z : ℂ) : ℂ :=
  (((y : ℝ) + 1 : ℝ) : ℂ) ^ (z - 1 / 2) * (_root_.RHTower.zetaEntire z * M z - (z - 1))

theorem differentiable_prefixField {M : ℂ → ℂ} (hM : Differentiable ℂ M) (y : ℕ) :
    Differentiable ℂ (prefixField M y) := by
  have hY : (((y : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : ((y : ℝ) + 1) ≠ 0)
  intro z
  exact (DifferentiableAt.const_cpow (differentiableAt_id.sub_const _) (Or.inl hY)).mul
    (((_root_.RHTower.differentiable_zetaEntire z).mul (hM z)).sub
      (differentiableAt_id.sub_const _))

theorem norm_prefixField_factor (y : ℕ) (z : ℂ) :
    ‖(((y : ℝ) + 1 : ℝ) : ℂ) ^ (z - 1 / 2)‖ = ((y : ℝ) + 1) ^ (z.re - 1 / 2) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

/-- **Quadratic growth of the prefix field** on `Re z ≥ ½`. -/
theorem exists_norm_prefixField_le {M : ℂ → ℂ} {KM : ℝ}
    (hMb : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ KM) {c : ℕ → ℂ} {y : ℕ} {B : ℝ} (hy : 1 ≤ y)
    (hB : 0 ≤ B) (hE : ∀ s : ℂ, 1 < s.re → riemannZeta s * M s - 1 = LSeries c s)
    (hzero : ∀ n, n ≤ y → c n = 0) (hbound : ∀ n, y < n → ‖c n‖ ≤ B * n) :
    ∃ C : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re → ‖prefixField M y z‖ ≤ C * (‖z‖ + 2) ^ 2 := by
  obtain ⟨K, hK1, hK⟩ := _root_.RHTower.exists_norm_zetaEntire_le
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hY1 : (1 : ℝ) ≤ (y : ℝ) + 1 := by linarith
  set Y₀ : ℝ := ((y : ℝ) + 1) ^ (5 / 2 : ℝ) with hY₀
  have hY₀0 : 0 < Y₀ := by positivity
  have hKM0 : 0 ≤ max KM 0 := le_max_right _ _
  refine ⟨Y₀ * (K * max KM 0 + 1 + B * (2 / y)), fun z hz => ?_⟩
  have hsq1 : (1 : ℝ) ≤ (‖z‖ + 2) ^ 2 := by nlinarith [norm_nonneg z]
  have hsub : ‖z - 1‖ ≤ ‖z‖ + 2 := by
    calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖z‖ + 2 := by rw [norm_one]; linarith
  have hsub2 : ‖z - 1‖ ≤ (‖z‖ + 2) ^ 2 := hsub.trans (by nlinarith [norm_nonneg z])
  have hc0 : 0 ≤ K * max KM 0 + 1 + B * (2 / y) := by positivity
  rw [prefixField, norm_mul, norm_prefixField_factor]
  rcases le_or_gt z.re 3 with hz3 | hz3
  · have hfac : ((y : ℝ) + 1) ^ (z.re - 1 / 2) ≤ Y₀ :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    have hA : ‖_root_.RHTower.zetaEntire z * M z - (z - 1)‖ ≤
        (K * max KM 0 + 1 + B * (2 / y)) * (‖z‖ + 2) ^ 2 := by
      calc ‖_root_.RHTower.zetaEntire z * M z - (z - 1)‖
          ≤ ‖_root_.RHTower.zetaEntire z‖ * ‖M z‖ + ‖z - 1‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ K * (‖z‖ + 2) ^ 2 * max KM 0 + (‖z‖ + 2) ^ 2 := by
            have h1 := hK z hz
            have h2 := (hMb z hz).trans (le_max_left KM 0)
            have h3 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
            linarith
        _ ≤ (K * max KM 0 + 1 + B * (2 / y)) * (‖z‖ + 2) ^ 2 := by
            have : 0 ≤ B * (2 / y) * (‖z‖ + 2) ^ 2 := by positivity
            nlinarith
    calc ((y : ℝ) + 1) ^ (z.re - 1 / 2) * ‖_root_.RHTower.zetaEntire z * M z - (z - 1)‖
        ≤ Y₀ * ((K * max KM 0 + 1 + B * (2 / y)) * (‖z‖ + 2) ^ 2) :=
          mul_le_mul hfac hA (norm_nonneg _) hY₀0.le
      _ = Y₀ * (K * max KM 0 + 1 + B * (2 / y)) * (‖z‖ + 2) ^ 2 := by ring
  · have hz1 : z ≠ 1 := by
      rintro rfl
      simp at hz3
    have hfact : _root_.RHTower.zetaEntire z * M z - (z - 1) = (z - 1) * LSeries c z := by
      rw [← hE z (by linarith), _root_.RHTower.zetaEntire_eq hz1]
      ring
    have hL := norm_LSeries_le_rpow_of_vanishing_head hy hB hzero hbound (s := z) hz3.le
    rw [hfact, norm_mul]
    have hprod : ((y : ℝ) + 1) ^ (z.re - 1 / 2) * ((y : ℝ) + 1) ^ (3 - z.re) = Y₀ := by
      rw [← Real.rpow_add (by positivity), hY₀]
      congr 1
      ring
    have hb2 : 0 ≤ B * (2 / y) := by positivity
    calc ((y : ℝ) + 1) ^ (z.re - 1 / 2) * (‖z - 1‖ * ‖LSeries c z‖)
        ≤ ((y : ℝ) + 1) ^ (z.re - 1 / 2) *
            (‖z - 1‖ * (((y : ℝ) + 1) ^ (3 - z.re) * (B * (2 / y)))) := by
          gcongr
      _ = Y₀ * (B * (2 / y)) * ‖z - 1‖ := by rw [← hprod]; ring
      _ ≤ Y₀ * (B * (2 / y)) * (‖z‖ + 2) ^ 2 :=
          mul_le_mul_of_nonneg_left hsub2 (by positivity)
      _ ≤ Y₀ * (K * max KM 0 + 1 + B * (2 / y)) * (‖z‖ + 2) ^ 2 := by
          gcongr
          have : 0 ≤ K * max KM 0 := by positivity
          linarith

/-- The mollified error `ζM − 1` on the critical line. -/
def lineError (M : ℂ → ℂ) (u : ℝ) : ℂ := riemannZeta (linePoint u) * M (linePoint u) - 1

theorem prefixField_linePoint (M : ℂ → ℂ) (y : ℕ) (u : ℝ) :
    ‖prefixField M y (linePoint u)‖ = ‖linePoint u‖ * ‖lineError M u‖ := by
  have hne := linePoint_ne_one u
  have hsub : ‖linePoint u - 1‖ = ‖linePoint u‖ := by
    rw [linePoint, _root_.RHTower.norm_half_add_mul_I_sub_one, _root_.RHTower.norm_half_add_mul_I]
  rw [prefixField, norm_mul, norm_prefixField_factor, linePoint_re, sub_self, Real.rpow_zero,
    one_mul, _root_.RHTower.zetaEntire_eq hne, lineError]
  rw [show (linePoint u - 1) * riemannZeta (linePoint u) * M (linePoint u) - (linePoint u - 1) =
    (linePoint u - 1) * (riemannZeta (linePoint u) * M (linePoint u) - 1) by ring, norm_mul, hsub]

/-- **The logarithmic floor.** Let `M` be entire and bounded on `Re s ≥ ½`, and let the coefficients of `ζM − 1` vanish up to `y`,
with `|c_n| ≤ Bn` beyond. Then every zero `ρ` of `ζ` with `½ < Re ρ < 1` satisfies
`∫ P_ρ log |ζM − 1|(½ + iu) du ≥ (Re ρ − ½) log (y + 1) − log (|ρ|/|1 − ρ|)`. -/
theorem integrable_and_poisson_log_floor {M : ℂ → ℂ} (hM : Differentiable ℂ M) {KM : ℝ}
    (hMb : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖M s‖ ≤ KM) {c : ℕ → ℂ} {y : ℕ} {B : ℝ} (hy : 1 ≤ y)
    (hB : 0 ≤ B) (hE : ∀ s : ℂ, 1 < s.re → riemannZeta s * M s - 1 = LSeries c s)
    (hzero : ∀ n, n ≤ y → c n = 0) (hbound : ∀ n, y < n → ‖c n‖ ≤ B * n) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) (hre1 : ρ.re < 1) :
    Integrable (fun u : ℝ =>
        halfPlanePoisson (ρ.re - 1 / 2) (u - ρ.im) * Real.log ‖lineError M u‖) ∧
      (ρ.re - 1 / 2) * Real.log ((y : ℝ) + 1) - Real.log (‖ρ‖ / ‖1 - ρ‖) ≤
        ∫ u : ℝ, halfPlanePoisson (ρ.re - 1 / 2) (u - ρ.im) * Real.log ‖lineError M u‖ := by
  set δ : ℝ := ρ.re - 1 / 2 with hδdef
  set γ : ℝ := ρ.im with hγdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ < 1 / 2 := by rw [hδdef]; linarith
  have hpt : offLinePoint δ γ = ρ := by
    apply Complex.ext
    · rw [offLinePoint_re, hδdef]; ring
    · rw [offLinePoint_im]
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp at hre1
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    simp at hre
    linarith
  have hsub0 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hG : Differentiable ℂ (prefixField M y) := differentiable_prefixField hM y
  obtain ⟨C, hC⟩ := exists_norm_prefixField_le hMb hy hB hE hzero hbound
  have hY0 : (0 : ℝ) < (y : ℝ) + 1 := by positivity
  have hval : prefixField M y ρ =
      (((y : ℝ) + 1 : ℝ) : ℂ) ^ (ρ - 1 / 2) * (-(ρ - 1)) := by
    rw [prefixField, _root_.RHTower.zetaEntire_eq hρ1, hζ]
    ring_nf
  have hYne : (((y : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hY0.ne'
  have hne : prefixField M y ρ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hYne h.1) (neg_ne_zero.mpr hsub0)
  have hjensen := integrable_and_log_norm_le_poisson hG hC hδ (by rw [hpt]; exact hne)
  obtain ⟨hint, hle⟩ := hjensen
  obtain ⟨hintL, hL⟩ := integrable_and_integral_poisson_log_norm_line hδ hδ1 γ
  rw [hpt] at hle hL
  have hae : ∀ᵐ u : ℝ, Real.log ‖prefixField M y (linePoint u)‖ =
      Real.log ‖linePoint u‖ + Real.log ‖lineError M u‖ := by
    have hcount := _root_.RHTower.countable_setOf_eq_zero_of_differentiable hG hne
    have hpre : {u : ℝ | prefixField M y (linePoint u) = 0}.Countable :=
      hcount.preimage_of_injOn (linePoint_injective.injOn)
    filter_upwards [hpre.ae_notMem volume] with u hu
    have hu' : prefixField M y (linePoint u) ≠ 0 := hu
    have hnorm := prefixField_linePoint M y u
    have hn0 : ‖prefixField M y (linePoint u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu'
    rw [hnorm] at hn0 ⊢
    exact Real.log_mul (left_ne_zero_of_mul hn0) (right_ne_zero_of_mul hn0)
  have heq : (fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log ‖lineError M u‖) =ᵐ[volume]
      fun u => halfPlanePoisson δ (u - γ) * Real.log ‖prefixField M y (linePoint u)‖ -
        halfPlanePoisson δ (u - γ) * Real.log ‖linePoint u‖ := by
    filter_upwards [hae] with u hu
    rw [hu]
    ring
  have hintE : Integrable fun u : ℝ =>
      halfPlanePoisson δ (u - γ) * Real.log ‖lineError M u‖ :=
    (hint.sub hintL).congr heq.symm
  refine ⟨hintE, ?_⟩
  rw [integral_congr_ae heq, integral_sub hint hintL, hL]
  have hnormval : ‖prefixField M y ρ‖ = ((y : ℝ) + 1) ^ δ * ‖1 - ρ‖ := by
    rw [hval, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY0, norm_neg]
    have hrew : (ρ - 1 / 2).re = δ := by simp [hδdef]
    rw [hrew, ← norm_neg (ρ - 1), neg_sub]
  have hn1 : 0 < ‖1 - ρ‖ := by
    rw [← norm_neg, neg_sub]
    exact norm_pos_iff.mpr hsub0
  have hlogval : Real.log ‖prefixField M y ρ‖ =
      δ * Real.log ((y : ℝ) + 1) + Real.log ‖1 - ρ‖ := by
    rw [hnormval, Real.log_mul (by positivity) hn1.ne', Real.log_rpow hY0]
  rw [Real.log_div (norm_ne_zero_iff.mpr hρ0) hn1.ne']
  linarith

/-- The Poisson density is a probability density. -/
theorem integrable_poisson_shift {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    Integrable fun u : ℝ => halfPlanePoisson δ (u - γ) :=
  (integrable_halfPlanePoisson hδ).comp_sub_right γ

theorem integral_poisson_shift {δ : ℝ} (hδ : 0 < δ) (γ : ℝ) :
    ∫ u : ℝ, halfPlanePoisson δ (u - γ) = 1 := by
  rw [integral_sub_right_eq_self (fun u => halfPlanePoisson δ u) γ]
  exact integral_halfPlanePoisson hδ

/-- **The floor at every exponent.** If `|E|^p` is integrable against `P_ρ`, then its `P_ρ`-mean is at least the exponential of `p` times
the logarithmic mean of `|E|`. -/
theorem exp_mul_le_integral_poisson_norm_rpow {δ γ p : ℝ} (hδ : 0 < δ) (hp : 0 < p) {E : ℝ → ℂ}
    (hlog : Integrable fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log ‖E u‖)
    (hne : ∀ᵐ u : ℝ, E u ≠ 0)
    (hint : Integrable fun u : ℝ => halfPlanePoisson δ (u - γ) * ‖E u‖ ^ p) :
    Real.exp (p * ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log ‖E u‖) ≤
      ∫ u : ℝ, halfPlanePoisson δ (u - γ) * ‖E u‖ ^ p := by
  set L : ℝ := ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log ‖E u‖ with hL
  set a : ℝ := Real.exp (p * L) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have hP := integrable_poisson_shift hδ γ
  -- `log x ≤ x / a + log a − 1` at `x = |E|^p`.
  have hpt : ∀ᵐ u : ℝ, p * (halfPlanePoisson δ (u - γ) * Real.log ‖E u‖) ≤
      a⁻¹ * (halfPlanePoisson δ (u - γ) * ‖E u‖ ^ p) +
        (p * L - 1) * halfPlanePoisson δ (u - γ) := by
    filter_upwards [hne] with u hu
    have hP0 : 0 ≤ halfPlanePoisson δ (u - γ) := (halfPlanePoisson_pos hδ _).le
    have hn : 0 < ‖E u‖ := norm_pos_iff.mpr hu
    have hx : 0 < ‖E u‖ ^ p := Real.rpow_pos_of_pos hn p
    have hl := Real.log_le_sub_one_of_pos (div_pos hx ha0)
    rw [Real.log_div hx.ne' ha0.ne', Real.log_rpow hn, ha, Real.log_exp] at hl
    have hl' : p * Real.log ‖E u‖ ≤ a⁻¹ * ‖E u‖ ^ p + (p * L - 1) := by
      rw [ha]
      rw [div_eq_inv_mul] at hl
      linarith
    calc p * (halfPlanePoisson δ (u - γ) * Real.log ‖E u‖)
        = halfPlanePoisson δ (u - γ) * (p * Real.log ‖E u‖) := by ring
      _ ≤ halfPlanePoisson δ (u - γ) * (a⁻¹ * ‖E u‖ ^ p + (p * L - 1)) :=
          mul_le_mul_of_nonneg_left hl' hP0
      _ = _ := by ring
  have hI : Integrable fun u : ℝ => a⁻¹ * (halfPlanePoisson δ (u - γ) * ‖E u‖ ^ p) +
      (p * L - 1) * halfPlanePoisson δ (u - γ) :=
    (hint.const_mul a⁻¹).add (hP.const_mul (p * L - 1))
  have hmono := integral_mono_ae (hlog.const_mul p) hI hpt
  rw [integral_const_mul] at hmono
  rw [integral_add (hint.const_mul a⁻¹) (hP.const_mul (p * L - 1)), integral_const_mul,
    integral_const_mul, integral_poisson_shift hδ γ, mul_one] at hmono
  have h1 : 1 ≤ a⁻¹ * ∫ u : ℝ, halfPlanePoisson δ (u - γ) * ‖E u‖ ^ p := by linarith
  rwa [← div_eq_inv_mul, one_le_div ha0] at h1

/-! ### The Möbius mollifier -/

/-- `M_X` as a function. -/
abbrev moebiusPoly (X : ℕ) : ℂ → ℂ :=
  _root_.RHTower.edPoly _root_.RHTower.mobCoeff (Finset.Icc 1 X)

theorem differentiable_moebiusPoly (X : ℕ) : Differentiable ℂ (moebiusPoly X) :=
  _root_.RHTower.differentiable_edPoly _ fun _ hn => (Finset.mem_Icc.mp hn).1

/-- **The logarithmic floor of the Möbius mollifier**, at every length. -/
theorem integrable_and_moebius_poisson_log_floor {X : ℕ} (hX : 1 ≤ X) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) (hre1 : ρ.re < 1) :
    Integrable (fun u : ℝ =>
        halfPlanePoisson (ρ.re - 1 / 2) (u - ρ.im) * Real.log ‖lineError (moebiusPoly X) u‖) ∧
      (ρ.re - 1 / 2) * Real.log ((X : ℝ) + 1) - Real.log (‖ρ‖ / ‖1 - ρ‖) ≤
        ∫ u : ℝ, halfPlanePoisson (ρ.re - 1 / 2) (u - ρ.im) *
          Real.log ‖lineError (moebiusPoly X) u‖ :=
  integrable_and_poisson_log_floor (differentiable_moebiusPoly X)
    (KM := X) (fun _ hs => _root_.RHTower.norm_edPoly_mobCoeff_le X (by linarith)) hX zero_le_one
    (c := _root_.RHTower.mobTailCoeff X)
    (fun _ hs => _root_.RHTower.mobMollifiedError_eq_LSeries X hs)
    (fun _ hn => _root_.RHTower.mobTailCoeff_eq_zero_of_le hn)
    (fun n hn => by simpa using _root_.RHTower.norm_mobTailCoeff_le hX hn) hζ hre hre1

end GaloisForLFunctions.MultiscaleMollifiedZetaField
