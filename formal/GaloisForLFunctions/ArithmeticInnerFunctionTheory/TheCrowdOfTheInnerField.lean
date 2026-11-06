import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheInnerMassIsAMollifierInfimum
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZeroForcesALogarithmicFloor
import GaloisForLFunctions.Bottcher.ZeroSet

/-!
# Depth, shadow, crowd: the hyperbolic geometry of the inner field

Hyperbolic geometry of `Re s > ½`. A zero `ρ = ½ + b + iγ` has a **shadow** `[γ − b, γ + b]` on the line. A **box** at the
centre `w = ½ + x + it` of ratio `θ` is the set of `ρ` with `θx ≤ b ≤ x`, `|γ − t| ≤ x`.

* **The Green kernel and the Carleson test** (`greenKernel_ge`). `G(w, ρ) ≥ 2xb/|w + ρ̄ − 1|²`, the normalized reproducing
  kernel test of the Carleson measure `Σ_ρ b_ρ δ_ρ`. So the inner field dominates the Carleson test.
* **A box is an exact budget** (`mult_sum_box_le`). Zeros in a box of ratio `θ` have total multiplicity at most `5/(2θ)` times
  `I(w)`, and for every mollifier `M` (`mult_sum_box_le_log_budget`)

  `(2θ/5) Σ m_ρ ≤ ½ log ∫ |ζM|² P_w − log |E(w) M(w)|`.

* **The arithmetic embedding** (`sum_weight_norm_sq_le_integral`). For an entire `A` of quadratic growth and any weights
  `Σ_ρ ν_ρ |A(ρ)|² ≤ ∫ |A(½ + iτ)|² (Σ_ρ ν_ρ P_ρ(τ)) dτ`. The kernel on the right is the balayage of the weighted
  zeros to the line, the **crowd**; with `ν_ρ = b_ρ` it is at least `1/(2π)` times the number of shadows over `τ`
  (`shadow_count_le_crowd`), and the shadows have total length `2Σ b_ρ` (`volume_shadows_le`). A bounded crowd is the
  Carleson embedding at the critical scale, with arithmetic coefficients.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

local notation "𝕋" => AddCircle (2 * π)

/-! ### The Green kernel -/

/-- The polarization `|ρ + w̄ − 1|² = |ρ − w|² + 4xb`. -/
theorem sq_norm_add_conj_eq (w ρ : ℂ) :
    ‖ρ + conj w - 1‖ ^ 2 = ‖ρ - w‖ ^ 2 + 4 * (w.re - 1 / 2) * (ρ.re - 1 / 2) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
    Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
  ring

/-- **The Carleson test.** `G(w, ρ) ≥ 2xb/|ρ + w̄ − 1|²`. -/
theorem greenKernel_ge {w ρ : ℂ} (hw : 1 / 2 < w.re) (hρ : 1 / 2 < ρ.re) (hne : ρ ≠ w) :
    2 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / ‖ρ + conj w - 1‖ ^ 2 ≤ greenKernel w ρ := by
  have hA : 0 < ‖ρ + conj w - 1‖ := norm_pos_iff.mpr (ne_zero_of_half_lt_re hw hρ)
  have hB : 0 < ‖ρ - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hpol := sq_norm_add_conj_eq w ρ
  set A := ‖ρ + conj w - 1‖ with hAd
  set B := ‖ρ - w‖ with hBd
  have hlog : Real.log (B ^ 2 / A ^ 2) ≤ B ^ 2 / A ^ 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hG : greenKernel w ρ = -(1 / 2) * Real.log (B ^ 2 / A ^ 2) := by
    rw [greenKernel, ← hAd, ← hBd, ← div_pow, Real.log_pow, show A / B = (B / A)⁻¹ by
      rw [inv_div], Real.log_inv]
    push_cast
    ring
  have hfrac : 1 - B ^ 2 / A ^ 2 = 4 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / A ^ 2 := by
    field_simp
    linarith
  rw [hG]
  have e : 2 * (w.re - 1 / 2) * (ρ.re - 1 / 2) / A ^ 2 = (1 / 2) * (1 - B ^ 2 / A ^ 2) := by
    rw [hfrac]
    ring
  rw [e]
  linarith

/-- The box of ratio `θ` at the centre `w`. -/
def InBox (w : ℂ) (θ : ℝ) (ρ : ℂ) : Prop :=
  θ * (w.re - 1 / 2) ≤ ρ.re - 1 / 2 ∧ ρ.re - 1 / 2 ≤ w.re - 1 / 2 ∧ |ρ.im - w.im| ≤ w.re - 1 / 2

/-- **Every zero of a box costs at least `2θ/5`.** -/
theorem greenKernel_box_ge {w ρ : ℂ} {θ : ℝ} (hw : 1 / 2 < w.re) (hθ : 0 < θ) (hbox : InBox w θ ρ)
    (hne : ρ ≠ w) : 2 * θ / 5 ≤ greenKernel w ρ := by
  have hx : 0 < w.re - 1 / 2 := by linarith
  obtain ⟨h1, h2, h3⟩ := hbox
  have hb : 0 < ρ.re - 1 / 2 := lt_of_lt_of_le (mul_pos hθ hx) h1
  have hρ : 1 / 2 < ρ.re := by linarith
  refine le_trans ?_ (greenKernel_ge hw hρ hne)
  have hA : ‖ρ + conj w - 1‖ ^ 2 ≤ 5 * (w.re - 1 / 2) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im, sub_zero]
    have h4 : (ρ.im - w.im) ^ 2 ≤ (w.re - 1 / 2) ^ 2 := by
      rw [← sq_abs (ρ.im - w.im)]
      exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have h5 : ρ.re + w.re - 1 = (ρ.re - 1 / 2) + (w.re - 1 / 2) := by ring
    have h6 : (ρ.re + w.re - 1) ^ 2 ≤ (2 * (w.re - 1 / 2)) ^ 2 := by
      rw [h5]
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h7 : ρ.im + -w.im = ρ.im - w.im := by ring
    rw [h7]
    nlinarith
  have hApos : 0 < ‖ρ + conj w - 1‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (ne_zero_of_half_lt_re hw hρ)) 2
  rw [div_le_div_iff₀ (by norm_num) hApos]
  have h8 : 2 * θ * (w.re - 1 / 2) ^ 2 ≤ 2 * (w.re - 1 / 2) * (ρ.re - 1 / 2) := by
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hx.le)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hA (mul_pos (by norm_num : (0 : ℝ) < 2) hθ).le]

/-- **A box is at most `5/(2θ)` times the inner field.** -/
theorem mult_sum_box_le {w : ℂ} {θ : ℝ} (hw : 1 / 2 < w.re) (h0 : zetaEntire w ≠ 0) (hθ : 0 < θ)
    (Z : Finset ZetaRightZero) (hZ : ∀ ρ ∈ Z, InBox w θ ρ) :
    (2 * θ / 5) * ∑ ρ ∈ Z, zeroMult ρ ≤ innerField w := by
  have hsum := hasSum_innerField hw h0
  have hne : ∀ a : ZetaRightZero, (a : ℂ) ≠ w := fun a h => by
    apply h0
    rw [← h, zetaEntire_eq_zero_iff]
    exact a.2.1
  have hnn : ∀ a : ZetaRightZero, 0 ≤ zeroMult a * greenKernel w a := fun a =>
    mul_nonneg (zeroMult_pos a).le (greenKernel_pos hw a.2.2 (hne a)).le
  refine le_trans ?_ (sum_le_hasSum Z (fun a _ => hnn a) hsum)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (greenKernel_box_ge hw hθ (hZ ρ hρ) (hne ρ)) (zeroMult_pos ρ).le

/-! ### Jensen on the circle chart -/

/-- A weight read through the chart of `w`. -/
theorem exp_poisson_log_le_of_pos {w : ℂ} (hw : 1 / 2 < w.re) {W : ℝ → ℝ}
    (hpos : ∀ᵐ τ : ℝ, 0 < W τ)
    (hi : Integrable fun τ => W τ * halfPlanePoissonKernel w τ)
    (hl : Integrable fun τ => Real.log (W τ) * halfPlanePoissonKernel w τ) :
    Real.exp (∫ τ, Real.log (W τ) * halfPlanePoissonKernel w τ) ≤
      ∫ τ, W τ * halfPlanePoissonKernel w τ := by
  -- Jensen for the probability density `P_w`
  have hP0 : ∀ τ, 0 ≤ halfPlanePoissonKernel w τ := fun τ => (halfPlanePoissonKernel_pos hw τ).le
  have hPm : Measurable (fun τ : ℝ => halfPlanePoissonKernel w τ) := by
    unfold halfPlanePoissonKernel
    fun_prop
  have hmass : ∫ τ, halfPlanePoissonKernel w τ = 1 := by
    have h := (circleAverage_shift_eq_poisson hw (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      (fun _ => rfl)).2
    simpa [Real.circleAverage_const] using h.symm
  set ν : Measure ℝ := volume.withDensity (fun τ => ENNReal.ofReal (halfPlanePoissonKernel w τ)) with hν
  have hνprob : IsProbabilityMeasure ν := by
    constructor
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ hP0), hmass, ENNReal.ofReal_one]
    refine (integrable_of_integral_eq_one hmass)
  have hrw : ∀ g : ℝ → ℝ, ∫ τ, g τ ∂ν = ∫ τ, g τ * halfPlanePoissonKernel w τ := by
    intro g
    rw [hν, integral_withDensity_eq_integral_toReal_smul₀ hPm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp [ENNReal.toReal_ofReal (hP0 τ), mul_comm]
  have hint : ∀ g : ℝ → ℝ, Integrable (fun τ => g τ * halfPlanePoissonKernel w τ) → Integrable g ν := by
    intro g hg
    rw [hν, integrable_withDensity_iff_integrable_smul₀' hPm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine hg.congr (ae_of_all _ fun τ => ?_)
    simp [ENNReal.toReal_ofReal (hP0 τ), mul_comm]
  have hposν : ∀ᵐ τ ∂ν, 0 < W τ := by
    rw [hν]
    exact (withDensity_absolutelyContinuous _ _).ae_le hpos
  have := exp_integral_log_le (μ := ν) (g := fun _ => 0) hposν (hint _ hi) (hint _ hl)
    measurable_const ⟨0, fun _ => by simp⟩ (by simp)
  simpa [hrw] using this

/-- The zeros of an entire function nonzero at `w` have null trace on the line. -/
theorem ae_ne_zero_line {A : ℂ → ℂ} (hA : Differentiable ℂ A) {w : ℂ} (h0 : A w ≠ 0) :
    ∀ᵐ τ : ℝ, A (1 / 2 + τ * I) ≠ 0 := by
  have hc := Bottcher.analyticOnNhd_zeros_countable (f := A) (U := univ)
    (fun z _ => hA.analyticAt z) isPreconnected_univ (mem_univ w) h0
  have hinj : Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + τ * I) := by
    intro a b hab
    have := congrArg Complex.im hab
    simpa using this
  have hc' : {τ : ℝ | A (1 / 2 + τ * I) = 0}.Countable :=
    (hc.preimage hinj).mono fun τ hτ => by simpa using hτ
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hc'.measure_zero _)] with τ hτ
  exact hτ

/-- The two forms of the Poisson mean agree. -/
theorem integrable_and_log_norm_le_poisson' {A : ℂ → ℂ} (hA : Differentiable ℂ A) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖A z‖ ≤ C * (‖z‖ + 2) ^ 2) {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : A w ≠ 0) :
    Integrable (fun τ : ℝ => Real.log ‖A (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) ∧
      Real.log ‖A w‖ ≤ ∫ τ : ℝ, Real.log ‖A (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ := by
  have hδ : 0 < w.re - 1 / 2 := by linarith
  have ew : MultiscaleMollifiedZetaField.offLinePoint (w.re - 1 / 2) w.im = w := by
    apply Complex.ext <;> simp [MultiscaleMollifiedZetaField.offLinePoint]
  have h := MultiscaleMollifiedZetaField.integrable_and_log_norm_le_poisson hA hgrow hδ
    (by rw [ew]; exact h0)
  rw [ew] at h
  have ek : ∀ u : ℝ, GaloisForLFunctions.HTGeometry.halfPlanePoisson (w.re - 1 / 2) (u - w.im) *
      Real.log ‖A (MultiscaleMollifiedZetaField.linePoint u)‖ =
      Real.log ‖A (1 / 2 + u * I)‖ * halfPlanePoissonKernel w u := by
    intro u
    simp only [GaloisForLFunctions.HTGeometry.halfPlanePoisson, halfPlanePoissonKernel,
      MultiscaleMollifiedZetaField.linePoint]
    ring
  simp only [ek] at h
  exact h

/-- `|A(w)|² ≤ ∫ |A|² P_w` for an entire function of quadratic growth. -/
theorem norm_sq_le_poisson {A : ℂ → ℂ} (hA : Differentiable ℂ A) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖A z‖ ≤ C * (‖z‖ + 2) ^ 2) {w : ℂ} (hw : 1 / 2 < w.re)
    (hi : Integrable fun τ : ℝ => ‖A (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel w τ) :
    ‖A w‖ ^ 2 ≤ ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel w τ := by
  rcases eq_or_ne (A w) 0 with h0 | h0
  · rw [h0, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact integral_nonneg fun τ => mul_nonneg (sq_nonneg _) (halfPlanePoissonKernel_pos hw τ).le
  obtain ⟨hl, hle⟩ := integrable_and_log_norm_le_poisson' hA hgrow hw h0
  have hpos : ∀ᵐ τ : ℝ, 0 < ‖A (1 / 2 + τ * I)‖ ^ 2 := by
    filter_upwards [ae_ne_zero_line hA h0] with τ hτ
    exact pow_pos (norm_pos_iff.mpr hτ) 2
  have hl2 : Integrable fun τ : ℝ => Real.log (‖A (1 / 2 + τ * I)‖ ^ 2) * halfPlanePoissonKernel w τ := by
    refine (hl.const_mul 2).congr (ae_of_all _ fun τ => ?_)
    simp only [Real.log_pow]
    push_cast
    ring
  have hJ := exp_poisson_log_le_of_pos hw hpos hi hl2
  have he : ∫ τ : ℝ, Real.log (‖A (1 / 2 + τ * I)‖ ^ 2) * halfPlanePoissonKernel w τ =
      2 * ∫ τ : ℝ, Real.log ‖A (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [Real.log_pow]
    push_cast
    ring
  rw [he] at hJ
  refine le_trans ?_ hJ
  rw [← Real.exp_log (pow_pos (norm_pos_iff.mpr h0) 2), Real.log_pow]
  refine Real.exp_le_exp.mpr ?_
  push_cast
  linarith

/-- **The arithmetic embedding.** For any weights `ν ≥ 0` at points of the half-plane,
`Σ_ρ ν_ρ |A(ρ)|² ≤ ∫ |A(½ + iτ)|² (Σ_ρ ν_ρ P_ρ(τ)) dτ`. -/
theorem sum_weight_norm_sq_le_integral {A : ℂ → ℂ} (hA : Differentiable ℂ A) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖A z‖ ≤ C * (‖z‖ + 2) ^ 2) (D : Finset ℂ) (ν : ℂ → ℝ)
    (hD : ∀ ρ ∈ D, 1 / 2 < ρ.re) (hν : ∀ ρ ∈ D, 0 ≤ ν ρ)
    (hi : ∀ ρ ∈ D, Integrable fun τ : ℝ => ‖A (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel ρ τ) :
    ∑ ρ ∈ D, ν ρ * ‖A ρ‖ ^ 2 ≤
      ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * ∑ ρ ∈ D, ν ρ * halfPlanePoissonKernel ρ τ := by
  have e : ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * ∑ ρ ∈ D, ν ρ * halfPlanePoissonKernel ρ τ =
      ∑ ρ ∈ D, ν ρ * ∫ τ : ℝ, ‖A (1 / 2 + τ * I)‖ ^ 2 * halfPlanePoissonKernel ρ τ := by
    simp_rw [Finset.mul_sum, ← integral_const_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      ring
    · intro ρ hρ
      refine ((hi ρ hρ).const_mul (ν ρ)).congr (ae_of_all _ fun τ => ?_)
      ring
  rw [e]
  exact Finset.sum_le_sum fun ρ hρ =>
    mul_le_mul_of_nonneg_left (norm_sq_le_poisson hA hgrow (hD ρ hρ) (hi ρ hρ)) (hν ρ hρ)

/-! ### The mollified budget -/

/-- **The budget inequality.** For every entire mollifier `M` of quadratic growth,
`exp (2 I(w)) |E(w) M(w)|² ≤ ∫ |ζM|² P_w`. -/
theorem exp_two_innerField_mul_le {M : ℂ → ℂ} (hM : Differentiable ℂ M) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖M z‖ ≤ C * (‖z‖ + 2) ^ 2) {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : zetaEntire w ≠ 0) (hMw : M w ≠ 0)
    (hi : Integrable fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
      halfPlanePoissonKernel w τ) :
    Real.exp (2 * innerField w) * (‖zetaEntire w‖ / ‖w‖ * ‖M w‖) ^ 2 ≤
      ∫ τ : ℝ, ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
        halfPlanePoissonKernel w τ := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  obtain ⟨hlM, hleM⟩ := integrable_and_log_norm_le_poisson' hM hgrow hw hMw
  have hlZ := integrable_log_zeta_poisson hw
  have hne1 : zetaEntire 1 ≠ 0 := zetaEntire_one_ne_zero
  have hzline : ∀ᵐ τ : ℝ, riemannZeta (1 / 2 + τ * I) ≠ 0 := by
    filter_upwards [ae_ne_zero_line differentiable_zetaEntire hne1] with τ hτ h
    exact hτ (zetaEntire_eq_zero_iff.mpr h)
  have hMline := ae_ne_zero_line hM hMw
  set W : ℝ → ℝ := fun τ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 with hW
  have hpos : ∀ᵐ τ : ℝ, 0 < W τ := by
    filter_upwards [hzline, hMline] with τ h1 h2
    exact mul_pos (pow_pos (norm_pos_iff.mpr h1) 2) (pow_pos (norm_pos_iff.mpr h2) 2)
  have hae : (fun τ : ℝ => Real.log (W τ) * halfPlanePoissonKernel w τ) =ᵐ[volume] fun τ =>
      2 * (Real.log ‖riemannZeta (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) +
        2 * (Real.log ‖M (1 / 2 + τ * I)‖ * halfPlanePoissonKernel w τ) := by
    filter_upwards [hzline, hMline] with τ h1 h2
    have h1' : ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h1)
    have h2' : ‖M (1 / 2 + τ * I)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h2)
    simp only [hW]
    rw [Real.log_mul h1' h2', Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hl : Integrable fun τ : ℝ => Real.log (W τ) * halfPlanePoissonKernel w τ :=
    ((hlZ.const_mul 2).add (hlM.const_mul 2)).congr hae.symm
  have hJ := exp_poisson_log_le_of_pos hw hpos hi hl
  rw [integral_congr_ae hae, integral_add (hlZ.const_mul 2) (hlM.const_mul 2), integral_const_mul,
    integral_const_mul, integral_log_zeta_poisson_eq] at hJ
  refine le_trans ?_ hJ
  have hE : 0 < ‖zetaEntire w‖ := norm_pos_iff.mpr h0
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hMn : 0 < ‖M w‖ := norm_pos_iff.mpr hMw
  have e : Real.exp (2 * innerField w) * (‖zetaEntire w‖ / ‖w‖ * ‖M w‖) ^ 2 =
      Real.exp (2 * (innerField w + (Real.log ‖zetaEntire w‖ - Real.log ‖w‖)) + 2 * Real.log ‖M w‖) := by
    have e1 : (‖zetaEntire w‖ / ‖w‖ * ‖M w‖) ^ 2 =
        Real.exp (2 * (Real.log ‖zetaEntire w‖ - Real.log ‖w‖) + 2 * Real.log ‖M w‖) := by
      rw [← Real.exp_log (show 0 < (‖zetaEntire w‖ / ‖w‖ * ‖M w‖) ^ 2 by positivity), Real.log_pow,
        Real.log_mul (by positivity) hMn.ne', Real.log_div hE.ne' hwn.ne']
      congr 1
      push_cast
      ring
    rw [e1, ← Real.exp_add]
    congr 1
    ring
  rw [e]
  refine Real.exp_le_exp.mpr ?_
  linarith

/-- **A box is bounded by the mollified budget.** -/
theorem mult_sum_box_le_log_budget {M : ℂ → ℂ} (hM : Differentiable ℂ M) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖M z‖ ≤ C * (‖z‖ + 2) ^ 2) {w : ℂ} (hw : 1 / 2 < w.re)
    (h0 : zetaEntire w ≠ 0) (hMw : M w ≠ 0)
    (hi : Integrable fun τ : ℝ => ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
      halfPlanePoissonKernel w τ) {θ : ℝ} (hθ : 0 < θ)
    (Z : Finset ZetaRightZero) (hZ : ∀ ρ ∈ Z, InBox w θ ρ) :
    (2 * θ / 5) * ∑ ρ ∈ Z, zeroMult ρ ≤
      (1 / 2) * Real.log (∫ τ : ℝ, ‖riemannZeta (1 / 2 + τ * I)‖ ^ 2 * ‖M (1 / 2 + τ * I)‖ ^ 2 *
        halfPlanePoissonKernel w τ) - Real.log (‖zetaEntire w‖ / ‖w‖ * ‖M w‖) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw; linarith
  have h1 := mult_sum_box_le hw h0 hθ Z hZ
  have h2 := exp_two_innerField_mul_le hM hgrow hw h0 hMw hi
  have hA : 0 < ‖zetaEntire w‖ / ‖w‖ * ‖M w‖ :=
    mul_pos (div_pos (norm_pos_iff.mpr h0) (norm_pos_iff.mpr hw0)) (norm_pos_iff.mpr hMw)
  have hlog := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-! ### Shadows and the crowd -/

/-- The shadow of a point of the half-plane on the line. -/
def shadow (ρ : ℂ) : Set ℝ := Icc (ρ.im - (ρ.re - 1 / 2)) (ρ.im + (ρ.re - 1 / 2))

/-- The crowd: the balayage of the Carleson measure of `D` to the line. -/
def crowd (D : Finset ℂ) (τ : ℝ) : ℝ := ∑ ρ ∈ D, (ρ.re - 1 / 2) * halfPlanePoissonKernel ρ τ

/-- Each shadow over `τ` contributes at least `1/(2π)` to the crowd. -/
theorem one_div_two_pi_le_of_mem_shadow {ρ : ℂ} (hρ : 1 / 2 < ρ.re) {τ : ℝ} (hτ : τ ∈ shadow ρ) :
    1 / (2 * π) ≤ (ρ.re - 1 / 2) * halfPlanePoissonKernel ρ τ := by
  have hb : 0 < ρ.re - 1 / 2 := by linarith
  have h1 : (τ - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
    apply sq_le_sq'
    · linarith [hτ.1]
    · linarith [hτ.2]
  unfold halfPlanePoissonKernel
  have hd : 0 < (ρ.re - 1 / 2) ^ 2 + (τ - ρ.im) ^ 2 := by positivity
  have hπ := Real.pi_pos
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

open scoped Classical in
/-- The number of shadows over `τ` is at most `2π` times the crowd. -/
theorem shadow_count_le_crowd {D : Finset ℂ} (hD : ∀ ρ ∈ D, 1 / 2 < ρ.re) (τ : ℝ) :
    ((D.filter fun ρ => τ ∈ shadow ρ).card : ℝ) ≤ 2 * π * crowd D τ := by
  have hπ := Real.pi_pos
  have h1 : ((D.filter fun ρ => τ ∈ shadow ρ).card : ℝ) * (1 / (2 * π)) ≤ crowd D τ := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine le_trans (Finset.sum_le_sum fun ρ hρ =>
      one_div_two_pi_le_of_mem_shadow (hD ρ (Finset.mem_filter.mp hρ).1)
        (Finset.mem_filter.mp hρ).2) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun ρ hρ _ => ?_
    exact mul_nonneg (by linarith [hD ρ hρ]) (halfPlanePoissonKernel_pos (hD ρ hρ) τ).le
  have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * π by positivity)
  have e : 2 * π * (((D.filter fun ρ => τ ∈ shadow ρ).card : ℝ) * (1 / (2 * π))) =
      ((D.filter fun ρ => τ ∈ shadow ρ).card : ℝ) := by
    field_simp
  linarith

/-- The shadows have total length at most `2 Σ b_ρ`. -/
theorem volume_shadows_le {D : Finset ℂ} (hD : ∀ ρ ∈ D, 1 / 2 < ρ.re) :
    (volume (⋃ ρ ∈ D, shadow ρ)).toReal ≤ 2 * ∑ ρ ∈ D, (ρ.re - 1 / 2) := by
  have h1 : volume (⋃ ρ ∈ D, shadow ρ) ≤ ∑ ρ ∈ D, volume (shadow ρ) :=
    measure_biUnion_finset_le _ _
  have h2 : ∀ ρ ∈ D, volume (shadow ρ) = ENNReal.ofReal (2 * (ρ.re - 1 / 2)) := by
    intro ρ _
    rw [shadow, Real.volume_Icc]
    congr 1
    ring
  rw [Finset.sum_congr rfl h2] at h1
  have hnn : ∀ ρ ∈ D, 0 ≤ 2 * (ρ.re - 1 / 2) := fun ρ hρ => by linarith [hD ρ hρ]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn] at h1
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg hnn), ← Finset.mul_sum] at h3
  exact h3

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
