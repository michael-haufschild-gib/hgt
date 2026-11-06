import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheHyperbolicDensityTheorem
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheExponentOfTheMollifiedErrorIsRigid

/-!
# The derivative reads the Blaschke factor

For a zero `ρ` of `ζ` with `b = Re ρ − ½ > 0`, let `P_ρ` be the Poisson density of `Re s > ½` seen from `ρ`. The **normalised derivative** is

`N(ρ) = 2b (|ρ − 1|/|ρ|) |ζ′(ρ)| exp(−∫ P_ρ log |ζ(½ + iu)| du)`.

**Theorem** (`normalDerivative_le_prod`). `N(ρ) ≤ Π_{a ∈ D} ϱ(ρ, a)` for every finite set `D` of zeros of `ζ` in `Re s > ½` other than `ρ`.

**Mechanism.** Dividing `E(z) = (z − 1)ζ(z)` by the Blaschke factors `(z − a)/(z + ā − 1)` of `D ∪ {ρ}` leaves an entire function of the same growth with the same modulus on the
critical line (`exists_blaschke_quotient`), whose value at `ρ` is `2b E′(ρ)/Π β_a(ρ)`. Poisson–Jensen at `ρ` for this quotient is the theorem (`blaschke_poisson_le`).

**A mollifier is outer.** Since `|M(ρ)| ≤ exp ∫ P_ρ log |M|`, a mollifier cannot raise the bound; it enters only when the logarithm is estimated by a second moment:
`|M(ρ)| exp ∫ P_ρ log |ζ| ≤ (∫ P_ρ |ζM|²)^{1/2}` (`norm_moebiusPoly_mul_exp_le_sqrt`).

**Consequences for the density of zeros near the line.**
* Zeros with a normal derivative obey the Density Hypothesis rate (`exists_card_zeros_with_normal_derivative_le`), and the same holds for the Möbius mollified field
  (`exists_card_zeros_with_normal_mollified_derivative_le`).
* A family of simple zeros whose negative second moment of `N` is `J` on average has size `≪ J (α + 1) T L e^{−2x}` (`exists_card_zeros_of_negative_moment_le`).
So the negative moments of `ζ′` at the zeros are exactly what stands between the mean-value theorem and the Density Hypothesis near the line.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### Dividing by finitely many Blaschke factors -/

theorem differentiable_dslope {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ) :
    Differentiable ℂ (dslope F a) :=
  differentiableOn_univ.mp ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hF.differentiableOn)

/-- On the critical line the reflected factor has the modulus of the factor. -/
theorem norm_reflect_line (a : ℂ) (u : ℝ) : ‖linePoint u + conj a - 1‖ = ‖linePoint u - a‖ := by
  have e : linePoint u + conj a - 1 = -conj (linePoint u - a) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.one_re, linePoint_re]
      ring
    · simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.conj_im, Complex.one_im, linePoint_im]
      ring
  rw [e, norm_neg, RCLike.norm_conj]

/-- One division by a Blaschke factor keeps the quadratic growth on `Re z ≥ ½`. -/
theorem blaschke_step_growth {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖F z‖ ≤ C * (‖z‖ + 2) ^ 2) {a : ℂ} (ha : 1 / 2 < a.re) (hFa : F a = 0) :
    ∃ C₁ : ℝ, ∀ z : ℂ, 1 / 2 ≤ z.re → ‖dslope F a z * (z + conj a - 1)‖ ≤ C₁ * (‖z‖ + 2) ^ 2 := by
  have hcont : Continuous fun z => dslope F a z * (z + conj a - 1) :=
    (differentiable_dslope hF a).continuous.mul (by fun_prop)
  obtain ⟨Ω, hΩ⟩ := (isCompact_closedBall a 1).exists_bound_of_continuousOn hcont.continuousOn
  have hb : 0 ≤ 2 * (a.re - 1 / 2) := by linarith
  have hC0 := abs_nonneg C
  have hΩ0 := abs_nonneg Ω
  have hC₁ : 0 ≤ |Ω| + (1 + 2 * (a.re - 1 / 2)) * |C| := by positivity
  refine ⟨|Ω| + (1 + 2 * (a.re - 1 / 2)) * |C|, fun z hz => ?_⟩
  have hs1 : (1 : ℝ) ≤ (‖z‖ + 2) ^ 2 := by nlinarith [norm_nonneg z]
  have hs0 : (0 : ℝ) ≤ (‖z‖ + 2) ^ 2 := by positivity
  by_cases h1 : ‖z - a‖ ≤ 1
  · have hmem : z ∈ Metric.closedBall a 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact h1
    have h4 : 0 ≤ (1 + 2 * (a.re - 1 / 2)) * |C| := by positivity
    calc ‖dslope F a z * (z + conj a - 1)‖ ≤ |Ω| := (hΩ z hmem).trans (le_abs_self _)
      _ ≤ (|Ω| + (1 + 2 * (a.re - 1 / 2)) * |C|) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hs1 hC₁
  · have h1' : 1 < ‖z - a‖ := not_le.mp h1
    have hza : z ≠ a := by
      rintro rfl
      rw [sub_self, norm_zero] at h1'
      linarith
    have hpos : 0 < ‖z - a‖ := by linarith
    rw [dslope_of_ne _ hza, slope_def_field, hFa, sub_zero]
    have hrefl : ‖z + conj a - 1‖ ≤ ‖z - a‖ + 2 * (a.re - 1 / 2) := by
      have e : z + conj a - 1 = (z - a) + ((2 * (a.re - 1 / 2) : ℝ) : ℂ) := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.ofReal_re]
          ring
        · simp only [Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im, Complex.ofReal_im]
          ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_of_nonneg hb]
    have hratio : ‖z + conj a - 1‖ / ‖z - a‖ ≤ 1 + 2 * (a.re - 1 / 2) := by
      rw [div_le_iff₀ hpos]
      nlinarith
    have hF1 : ‖F z‖ ≤ |C| * (‖z‖ + 2) ^ 2 :=
      (hgrow z hz).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs0)
    calc ‖F z / (z - a) * (z + conj a - 1)‖ = ‖F z‖ * (‖z + conj a - 1‖ / ‖z - a‖) := by
          rw [norm_mul, norm_div]
          ring
      _ ≤ (|C| * (‖z‖ + 2) ^ 2) * (1 + 2 * (a.re - 1 / 2)) :=
          mul_le_mul hF1 hratio (by positivity) (by positivity)
      _ = (1 + 2 * (a.re - 1 / 2)) * |C| * (‖z‖ + 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hs0

/-- **Division by a finite Blaschke product.** An entire function of quadratic growth on `Re z ≥ ½`, vanishing on `D ⊂ {Re z > ½}`, is `F · Π (z − a)/(z + ā − 1)`
with `F` entire, of the same growth and of the same modulus on the critical line. -/
theorem exists_blaschke_quotient {E : ℂ → ℂ} (hE : Differentiable ℂ E) {C₀ : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖E z‖ ≤ C₀ * (‖z‖ + 2) ^ 2) (D : Finset ℂ)
    (hD : ∀ a ∈ D, 1 / 2 < a.re ∧ E a = 0) :
    ∃ (F : ℂ → ℂ) (C : ℝ), Differentiable ℂ F ∧ (∀ z : ℂ, 1 / 2 ≤ z.re → ‖F z‖ ≤ C * (‖z‖ + 2) ^ 2) ∧
      (∀ u : ℝ, ‖F (linePoint u)‖ = ‖E (linePoint u)‖) ∧
      ∀ z : ℂ, E z * ∏ a ∈ D, (z + conj a - 1) = F z * ∏ a ∈ D, (z - a) := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨E, C₀, hE, hgrow, fun _ => rfl, fun z => by simp⟩
  | insert a D ha ih =>
    obtain ⟨F, C, hF, hC, hline, hid⟩ := ih fun b hb => hD b (Finset.mem_insert_of_mem hb)
    obtain ⟨ha1, ha0⟩ := hD a (Finset.mem_insert_self _ _)
    have hFa : F a = 0 := by
      have h := hid a
      rw [ha0, zero_mul] at h
      have hne : ∏ b ∈ D, (a - b) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun b hb => sub_ne_zero.mpr fun hab => ha (hab ▸ hb)
      exact (mul_eq_zero.mp h.symm).resolve_right hne
    obtain ⟨C₁, hC₁⟩ := blaschke_step_growth hF hC ha1 hFa
    refine ⟨fun z => dslope F a z * (z + conj a - 1), C₁,
      (differentiable_dslope hF a).mul (by fun_prop), hC₁, fun u => ?_, fun z => ?_⟩
    · have hza : linePoint u ≠ a := fun h => by
        have := congrArg Complex.re h
        rw [linePoint_re] at this
        linarith
      have hne : ‖linePoint u - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)
      show ‖dslope F a (linePoint u) * (linePoint u + conj a - 1)‖ = _
      rw [dslope_of_ne _ hza, slope_def_field, hFa, sub_zero, norm_mul, norm_div, norm_reflect_line,
        div_mul_cancel₀ _ hne, hline u]
    · rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have h2 : (z - a) * dslope F a z = F z := by
        have h3 := sub_smul_dslope F a z
        rw [hFa, sub_zero, smul_eq_mul] at h3
        exact h3
      linear_combination (z + conj a - 1) * hid z -
        (z + conj a - 1) * (∏ b ∈ D, (z - b)) * h2

/-- The pseudo-hyperbolic ratio is positive off the diagonal. -/
theorem hyperbolicRatio_pos_of_ne {ρ a : ℂ} (hρ : 1 / 2 < ρ.re) (ha : 1 / 2 < a.re) (hne : ρ ≠ a) :
    0 < hyperbolicRatio ρ a := by
  have h1 : ρ + conj a - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.zero_re] at this
    linarith
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) (norm_pos_iff.mpr h1)

/-- **Poisson–Jensen with a finite Blaschke product.** For `E` entire of quadratic growth with a simple zero at `ρ = ½ + δ + iγ` and further zeros `D`,
`log (2δ |E′(ρ)|/Π_{a ∈ D} ϱ(ρ, a)) ≤ ∫ P_ρ log |E(½ + iu)| du`. -/
theorem blaschke_poisson_le {E : ℂ → ℂ} (hE : Differentiable ℂ E) {C₀ : ℝ}
    (hgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖E z‖ ≤ C₀ * (‖z‖ + 2) ^ 2) {δ γ : ℝ} (hδ : 0 < δ) (D : Finset ℂ)
    (hρD : offLinePoint δ γ ∉ D) (hD : ∀ a ∈ D, 1 / 2 < a.re ∧ E a = 0) (hρ : E (offLinePoint δ γ) = 0)
    (hne : deriv E (offLinePoint δ γ) ≠ 0) :
    Integrable (fun u : ℝ => halfPlanePoisson δ (u - γ) * Real.log ‖E (linePoint u)‖) ∧
      Real.log (2 * δ * ‖deriv E (offLinePoint δ γ)‖ / ∏ a ∈ D, hyperbolicRatio (offLinePoint δ γ) a) ≤
        ∫ u : ℝ, halfPlanePoisson δ (u - γ) * Real.log ‖E (linePoint u)‖ := by
  classical
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = offLinePoint δ γ := ⟨_, rfl⟩
  rw [← hρdef] at hρD hρ hne ⊢
  have hρre : ρ.re = 1 / 2 + δ := by rw [hρdef, offLinePoint_re]
  obtain ⟨F, C, hF, hC, hline, hid⟩ := exists_blaschke_quotient hE hgrow D hD
  have hA : ∏ a ∈ D, (ρ - a) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a ha => sub_ne_zero.mpr fun h => hρD (h ▸ ha)
  have hR : ∏ a ∈ D, (ρ + conj a - 1) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a ha h => by
    have h1 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.zero_re] at h1
    have h2 := (hD a ha).1
    linarith
  have hFρ : F ρ = 0 := by
    have h := hid ρ
    rw [hρ, zero_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hA
  -- the derivative of the quotient at `ρ`
  have hdR : Differentiable ℂ fun z : ℂ => ∏ a ∈ D, (z + conj a - 1) := by fun_prop
  have hdA : Differentiable ℂ fun z : ℂ => ∏ a ∈ D, (z - a) := by fun_prop
  have h1 : HasDerivAt (fun z : ℂ => E z * ∏ a ∈ D, (z + conj a - 1))
      (deriv E ρ * ∏ a ∈ D, (ρ + conj a - 1) +
        E ρ * deriv (fun z : ℂ => ∏ a ∈ D, (z + conj a - 1)) ρ) ρ :=
    (hE ρ).hasDerivAt.mul (hdR ρ).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => F z * ∏ a ∈ D, (z - a))
      (deriv F ρ * ∏ a ∈ D, (ρ - a) + F ρ * deriv (fun z : ℂ => ∏ a ∈ D, (z - a)) ρ) ρ :=
    (hF ρ).hasDerivAt.mul (hdA ρ).hasDerivAt
  have hfun : (fun z : ℂ => E z * ∏ a ∈ D, (z + conj a - 1)) = fun z : ℂ => F z * ∏ a ∈ D, (z - a) :=
    funext hid
  rw [hfun] at h1
  have huniq := h1.unique h2
  rw [hρ, hFρ, zero_mul, zero_mul, add_zero, add_zero] at huniq
  -- the last Blaschke factor
  obtain ⟨F₁, hF₁def⟩ : ∃ F₁ : ℂ → ℂ, F₁ = fun z => dslope F ρ z * (z + conj ρ - 1) := ⟨_, rfl⟩
  have hF₁ : Differentiable ℂ F₁ := by
    rw [hF₁def]
    exact (differentiable_dslope hF ρ).mul (by fun_prop)
  have hρ1 : 1 / 2 < ρ.re := by linarith
  obtain ⟨C₁, hC₁⟩ := blaschke_step_growth hF hC hρ1 hFρ
  have hC₁' : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖F₁ z‖ ≤ C₁ * (‖z‖ + 2) ^ 2 := fun z hz => by
    rw [hF₁def]
    exact hC₁ z hz
  have hF₁line : ∀ u : ℝ, ‖F₁ (linePoint u)‖ = ‖E (linePoint u)‖ := fun u => by
    have hza : linePoint u ≠ ρ := fun h => by
      have := congrArg Complex.re h
      rw [linePoint_re] at this
      linarith
    have hn : ‖linePoint u - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hza)
    rw [hF₁def]
    show ‖dslope F ρ (linePoint u) * (linePoint u + conj ρ - 1)‖ = _
    rw [dslope_of_ne _ hza, slope_def_field, hFρ, sub_zero, norm_mul, norm_div, norm_reflect_line,
      div_mul_cancel₀ _ hn, hline u]
  have hρρ : ρ + conj ρ - 1 = ((2 * δ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, Complex.ofReal_re, hρre]
      ring
    · simp only [Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im, Complex.ofReal_im]
      ring
  have hF₁ρ : F₁ ρ = deriv F ρ * ((2 * δ : ℝ) : ℂ) := by
    rw [hF₁def]
    show dslope F ρ ρ * (ρ + conj ρ - 1) = _
    rw [dslope_same, hρρ]
  have hdF : deriv F ρ = deriv E ρ * (∏ a ∈ D, (ρ + conj a - 1)) / ∏ a ∈ D, (ρ - a) := by
    rw [eq_div_iff hA, huniq]
  have hprod : ∏ a ∈ D, hyperbolicRatio ρ a = ‖∏ a ∈ D, (ρ - a)‖ / ‖∏ a ∈ D, (ρ + conj a - 1)‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_div_distrib]
    rfl
  have hval : ‖F₁ ρ‖ = 2 * δ * ‖deriv E ρ‖ / ∏ a ∈ D, hyperbolicRatio ρ a := by
    have hAn : ‖∏ a ∈ D, (ρ - a)‖ ≠ 0 := norm_ne_zero_iff.mpr hA
    have hRn : ‖∏ a ∈ D, (ρ + conj a - 1)‖ ≠ 0 := norm_ne_zero_iff.mpr hR
    rw [hF₁ρ, hdF, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hprod]
    field_simp
  have h0 : F₁ ρ ≠ 0 := by
    rw [hF₁ρ, hdF]
    refine mul_ne_zero (div_ne_zero (mul_ne_zero hne hR) hA) ?_
    exact_mod_cast (by positivity : 2 * δ ≠ 0)
  have hJ := integrable_and_log_norm_le_poisson hF₁ hC₁' hδ (γ := γ) (by rw [← hρdef]; exact h0)
  rw [← hρdef, hval] at hJ
  simp only [hF₁line] at hJ
  exact hJ

/-! ### The zeta function -/

/-- The normalised derivative `2b (|ρ − 1|/|ρ|) |ζ′(ρ)| exp(−∫ P_ρ log |ζ|)` of a zero. -/
def normalDerivative (ρ : ℂ) : ℝ :=
  2 * (ρ.re - 1 / 2) * (‖ρ - 1‖ / ‖ρ‖) * ‖deriv riemannZeta ρ‖ *
    Real.exp (-∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖)

theorem normalDerivative_nonneg {ρ : ℂ} (hb : 1 / 2 ≤ ρ.re) : 0 ≤ normalDerivative ρ := by
  unfold normalDerivative
  have : 0 ≤ ρ.re - 1 / 2 := by linarith
  positivity

/-- The Poisson mean of `log |(z − 1)ζ(z)|` splits off `log |ρ|`. -/
theorem integrable_and_integral_poisson_log_zeta {ρ : ℂ} (hre : 1 / 2 < ρ.re) (hre1 : ρ.re < 1)
    (hint : Integrable fun u : ℝ => zeroPoisson ρ u * Real.log ‖_root_.RHTower.zetaEntire (linePoint u)‖) :
    Integrable (fun u : ℝ => zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖) ∧
      ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖_root_.RHTower.zetaEntire (linePoint u)‖ =
        Real.log ‖ρ‖ + ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ := by
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  have hδ1 : ρ.re - 1 / 2 < 1 / 2 := by linarith
  obtain ⟨hintL, hL⟩ := integrable_and_integral_poisson_log_norm_line hδ hδ1 ρ.im
  rw [offLinePoint_re_im] at hL
  have hcount := _root_.RHTower.countable_setOf_eq_zero_of_differentiable
    _root_.RHTower.differentiable_zetaEntire (x := 1) (by
      rw [_root_.RHTower.zetaEntire_eval_one]
      exact one_ne_zero)
  have hpre : {u : ℝ | _root_.RHTower.zetaEntire (linePoint u) = 0}.Countable :=
    hcount.preimage_of_injOn linePoint_injective.injOn
  have hae : ∀ᵐ u : ℝ, Real.log ‖_root_.RHTower.zetaEntire (linePoint u)‖ =
      Real.log ‖linePoint u‖ + Real.log ‖riemannZeta (linePoint u)‖ := by
    filter_upwards [hpre.ae_notMem volume] with u hu
    have hu' : _root_.RHTower.zetaEntire (linePoint u) ≠ 0 := hu
    have hsub : ‖linePoint u - 1‖ = ‖linePoint u‖ := by
      rw [linePoint, _root_.RHTower.norm_half_add_mul_I_sub_one, _root_.RHTower.norm_half_add_mul_I]
    have hnorm : ‖_root_.RHTower.zetaEntire (linePoint u)‖ = ‖linePoint u‖ * ‖riemannZeta (linePoint u)‖ := by
      rw [_root_.RHTower.zetaEntire_eq (linePoint_ne_one u), norm_mul, hsub]
    have hn0 : ‖_root_.RHTower.zetaEntire (linePoint u)‖ ≠ 0 := norm_ne_zero_iff.mpr hu'
    rw [hnorm] at hn0 ⊢
    exact Real.log_mul (left_ne_zero_of_mul hn0) (right_ne_zero_of_mul hn0)
  have heq : (fun u : ℝ => zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖) =ᵐ[volume]
      fun u => zeroPoisson ρ u * Real.log ‖_root_.RHTower.zetaEntire (linePoint u)‖ -
        zeroPoisson ρ u * Real.log ‖linePoint u‖ := by
    filter_upwards [hae] with u hu
    rw [hu]
    ring
  have hintZ : Integrable fun u : ℝ => zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ :=
    (hint.sub hintL).congr heq.symm
  refine ⟨hintZ, ?_⟩
  rw [integral_congr_ae heq, integral_sub hint hintL, hL]
  ring

/-- The derivative of `(z − 1)ζ(z)` at a zero of `ζ`. -/
theorem deriv_zetaEntire_of_zero {ρ : ℂ} (hρ1 : ρ ≠ 1) (hζ : riemannZeta ρ = 0) :
    deriv _root_.RHTower.zetaEntire ρ = (ρ - 1) * deriv riemannZeta ρ := by
  have hev : _root_.RHTower.zetaEntire =ᶠ[nhds ρ] fun s => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds hρ1] with s hs
    exact _root_.RHTower.zetaEntire_eq hs
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun s : ℂ => (s - 1) * riemannZeta s)
      (1 * riemannZeta ρ + (ρ - 1) * deriv riemannZeta ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const 1).mul (differentiableAt_riemannZeta hρ1).hasDerivAt
  rw [h1.deriv, hζ]
  ring

/-- **The derivative reads the Blaschke factor.** `N(ρ) ≤ Π_{a ∈ D} ϱ(ρ, a)` for every finite set `D` of other zeros of `ζ` in `½ < Re s < 1`. -/
theorem normalDerivative_le_prod {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) (hre1 : ρ.re < 1)
    (D : Finset ℂ) (hρD : ρ ∉ D) (hD : ∀ a ∈ D, 1 / 2 < a.re ∧ a.re < 1 ∧ riemannZeta a = 0) :
    normalDerivative ρ ≤ ∏ a ∈ D, hyperbolicRatio ρ a := by
  have hP : 0 < ∏ a ∈ D, hyperbolicRatio ρ a := Finset.prod_pos fun a ha =>
    hyperbolicRatio_pos_of_ne hre (hD a ha).1 fun h => hρD (h ▸ ha)
  by_cases hdz : deriv riemannZeta ρ = 0
  · unfold normalDerivative
    rw [hdz, norm_zero, mul_zero, zero_mul]
    exact hP.le
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp at hre1
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    simp at hre
    linarith
  have hsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  obtain ⟨K, -, hK⟩ := _root_.RHTower.exists_norm_zetaEntire_le
  have hzero : _root_.RHTower.zetaEntire ρ = 0 := by
    rw [_root_.RHTower.zetaEntire_eq hρ1, hζ, mul_zero]
  have hdE := deriv_zetaEntire_of_zero hρ1 hζ
  have hmain := blaschke_poisson_le (E := _root_.RHTower.zetaEntire) _root_.RHTower.differentiable_zetaEntire
    hK hδ (γ := ρ.im) D (by rw [offLinePoint_re_im]; exact hρD) (fun a ha => by
      obtain ⟨h1, h2, h3⟩ := hD a ha
      have ha1 : a ≠ 1 := by
        rintro rfl
        simp at h2
      exact ⟨h1, by rw [_root_.RHTower.zetaEntire_eq ha1, h3, mul_zero]⟩)
    (by rw [offLinePoint_re_im]; exact hzero)
    (by rw [offLinePoint_re_im, hdE]; exact mul_ne_zero hsub hdz)
  rw [offLinePoint_re_im, hdE] at hmain
  obtain ⟨hint, hle⟩ := hmain
  obtain ⟨-, hsplit⟩ := integrable_and_integral_poisson_log_zeta hre hre1 hint
  have hle' : Real.log (2 * (ρ.re - 1 / 2) * ‖(ρ - 1) * deriv riemannZeta ρ‖ /
      ∏ a ∈ D, hyperbolicRatio ρ a) ≤
      Real.log ‖ρ‖ + ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ := by
    rw [← hsplit]
    exact hle
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ := ⟨_, rfl⟩
  rw [← hZ] at hle'
  have hn0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hd0 : 0 < ‖deriv riemannZeta ρ‖ := norm_pos_iff.mpr hdz
  have hs0 : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr hsub
  have hX0 : 0 < 2 * (ρ.re - 1 / 2) * ‖(ρ - 1) * deriv riemannZeta ρ‖ / ∏ a ∈ D, hyperbolicRatio ρ a := by
    rw [norm_mul]
    positivity
  rw [Real.log_le_iff_le_exp hX0, Real.exp_add, Real.exp_log hn0, norm_mul, div_le_iff₀ hP] at hle'
  have e : normalDerivative ρ = 2 * (ρ.re - 1 / 2) * (‖ρ - 1‖ * ‖deriv riemannZeta ρ‖) /
      (‖ρ‖ * Real.exp Z) := by
    unfold normalDerivative
    rw [← hZ, Real.exp_neg]
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  calc _ ≤ ‖ρ‖ * Real.exp Z * ∏ a ∈ D, hyperbolicRatio ρ a := hle'
    _ = _ := by ring

/-- A zero on the critical line has pseudo-hyperbolic ratio one. -/
theorem hyperbolicRatio_eq_one_of_line {ρ a : ℂ} (ha : a.re = 1 / 2) (hne : ρ ≠ a) : hyperbolicRatio ρ a = 1 := by
  have e : ρ + conj a - 1 = ρ - a := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re, ha]
      ring
    · simp only [Complex.sub_im, Complex.add_im, Complex.conj_im, Complex.one_im]
      ring
  unfold hyperbolicRatio
  rw [e]
  exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))

/-- `N(ρ)` bounds the product over a finite family of zeros of the configuration in `Re s ≥ ½`. -/
theorem normalDerivative_le_prod_carrier (ρ : zetaZeroConfig.carrier) (hre : 1 / 2 < (ρ : ℂ).re)
    (D : Finset zetaZeroConfig.carrier) (hD : ∀ a ∈ D, 1 / 2 ≤ (a : ℂ).re) :
    normalDerivative (ρ : ℂ) ≤ ∏ a ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (a : ℂ) := by
  classical
  obtain ⟨hζ, -, hre1⟩ : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hfilter : ∏ a ∈ (D.erase ρ).filter (fun a : zetaZeroConfig.carrier => 1 / 2 < (a : ℂ).re),
      hyperbolicRatio (ρ : ℂ) (a : ℂ) = ∏ a ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (a : ℂ) := by
    refine Finset.prod_filter_of_ne fun a ha hne => ?_
    by_contra hlt
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp ha
    have hline : (a : ℂ).re = 1 / 2 := le_antisymm (not_lt.mp hlt) (hD a h2)
    exact hne (hyperbolicRatio_eq_one_of_line hline fun h => h1 (Subtype.ext h.symm))
  rw [← hfilter, ← Finset.prod_image (s := (D.erase ρ).filter
    (fun a : zetaZeroConfig.carrier => 1 / 2 < (a : ℂ).re)) (g := Subtype.val)
    (f := fun a => hyperbolicRatio (ρ : ℂ) a) Subtype.val_injective.injOn]
  refine normalDerivative_le_prod hζ hre hre1 _ (fun h => ?_) fun a ha => ?_
  · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp h
    exact (Finset.mem_erase.mp (Finset.mem_filter.mp hb).1).1 (Subtype.ext hbe)
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hζb, -, hb1⟩ : IsNontrivialZero (b : ℂ) := b.2
    exact ⟨(Finset.mem_filter.mp hb).2, hb1, hζb⟩

/-! ### Zeros with a normal derivative -/

/-- **Zeros with a normal derivative obey the Density Hypothesis rate.** Fix `0 < c ≤ 1/28800`, `x = (1−3c)α`, `x ≤ (3/2) c log T`. Separated zeros of depth in
`[α/L, (α+1)/L]` with `N(ρ) ≥ B₀ ≥ e^{−x/8}` number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L³ T^{1/2}`. -/
theorem exists_card_zeros_with_normal_derivative_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 28800) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α B₀ : ℝ, 0 ≤ α →
      (1 - 3 * c) * α ≤ 3 / 2 * (c * Real.log T) →
      Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧ B₀ ≤ normalDerivative (ρ : ℂ)) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC, hmain⟩ := exists_card_hyperbolically_isolated_zeros_unconditional_le hv hsupp hv0 hI hc0 hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT hL0 α B₀ hα hxL hB₀low hB₀1 S hS hsep
  have hB₀ : 0 < B₀ := lt_of_lt_of_le (Real.exp_pos _) hB₀low
  have h13 : 0 ≤ 1 - 3 * c := by linarith
  refine hT α B₀ hα hxL hB₀low hB₀1 S (fun ρ hρ => ?_) hsep
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS ρ hρ
  refine ⟨h1, h2, h3, h4, fun D hρD hD => ?_⟩
  have hb0 : 0 ≤ (ρ : ℂ).re - 1 / 2 := le_trans (by positivity) h1
  have hre : 1 / 2 < (ρ : ℂ).re := by
    rcases hb0.lt_or_eq with h | h
    · linarith
    · exfalso
      have hN : normalDerivative (ρ : ℂ) = 0 := by
        unfold normalDerivative
        rw [← h]
        ring
      linarith
  refine h5.trans (normalDerivative_le_prod_carrier ρ hre D fun a ha => ?_)
  have h6 : 0 ≤ (1 - 3 * c) * α / 2 / Real.log T := by positivity
  have h7 := hD a ha
  linarith

/-- **A negative moment pays the Density Hypothesis rate.** Fix `0 < c ≤ 1/28800`, `x = (1−3c)α`, `x ≤ (3/2) c log T`, and `½ ≤ J`, `2J ≤ e^{x/4}`. A separated family of zeros of depth in
`[α/L, (α+1)/L]` with `N(ρ) ≠ 0` and `Σ N(ρ)^{−2} ≤ J · #S` has `#S ≪_c J (α+1) T L e^{−2(1−3c)α} + L³ T^{1/2}`. -/
theorem exists_card_zeros_of_negative_moment_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 28800) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α J : ℝ, 0 ≤ α →
      (1 - 3 * c) * α ≤ 3 / 2 * (c * Real.log T) → 1 / 2 ≤ J →
      2 * J ≤ Real.exp ((1 - 3 * c) * α / 4) →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧ normalDerivative (ρ : ℂ) ≠ 0) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      ∑ ρ ∈ S, (normalDerivative (ρ : ℂ) ^ 2)⁻¹ ≤ J * S.card →
      (S.card : ℝ) ≤ C * J * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) +
        C * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2)) := by
  classical
  obtain ⟨C, hC, hmain⟩ := exists_card_zeros_with_normal_derivative_le hv hsupp hv0 hI hc0 hc
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [hmain, Real.tendsto_log_atTop.eventually_gt_atTop 0, eventually_gt_atTop 0]
    with T hT hL0 hT0 α J hα hxL hJ hJx S hS hsep hmom
  have hJ0 : 0 < J := by linarith
  have h13 : 0 ≤ 1 - 3 * c := by linarith
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, B₀ = Real.sqrt (1 / (2 * J)) := ⟨_, rfl⟩
  have hsq : B₀ ^ 2 = 1 / (2 * J) := by
    rw [hB₀, Real.sq_sqrt (by positivity)]
  have hB₀0 : 0 < B₀ := by
    rw [hB₀]
    exact Real.sqrt_pos.mpr (by positivity)
  have hB₀1 : B₀ ≤ 1 := by
    rw [hB₀, Real.sqrt_le_one, div_le_one (by positivity)]
    linarith
  have hB₀low : Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ := by
    rw [hB₀]
    refine Real.le_sqrt_of_sq_le ?_
    rw [← Real.exp_nat_mul]
    have e : ((2 : ℕ) : ℝ) * -((1 - 3 * c) * α / 8) = -((1 - 3 * c) * α / 4) := by
      push_cast
      ring
    rw [e, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) hJx
  -- the zeros with a normal derivative carry half the family
  obtain ⟨S₁, hS₁⟩ : ∃ S₁, S₁ = S.filter fun ρ : zetaZeroConfig.carrier => B₀ ≤ normalDerivative (ρ : ℂ) := ⟨_, rfl⟩
  have hcount := hT α B₀ hα hxL hB₀low hB₀1 S₁ (fun ρ hρ => by
      rw [hS₁] at hρ
      obtain ⟨h0, h5⟩ := Finset.mem_filter.mp hρ
      obtain ⟨h1, h2, h3, h4, -⟩ := hS ρ h0
      exact ⟨h1, h2, h3, h4, h5⟩)
    (fun ρ hρ ρ' hρ' hne => by
      rw [hS₁] at hρ hρ'
      exact hsep ρ (Finset.mem_filter.mp hρ).1 ρ' (Finset.mem_filter.mp hρ').1 hne)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S)
    (fun ρ : zetaZeroConfig.carrier => B₀ ≤ normalDerivative (ρ : ℂ))
  have hsmall : 2 * J * (((S.filter fun ρ : zetaZeroConfig.carrier =>
      ¬ B₀ ≤ normalDerivative (ρ : ℂ)).card : ℕ) : ℝ) ≤ J * S.card := by
    refine le_trans ?_ hmom
    have h1 : ∑ ρ ∈ S.filter (fun ρ : zetaZeroConfig.carrier => ¬ B₀ ≤ normalDerivative (ρ : ℂ)),
        (normalDerivative (ρ : ℂ) ^ 2)⁻¹ ≤ ∑ ρ ∈ S, (normalDerivative (ρ : ℂ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    refine le_trans ?_ h1
    rw [mul_comm, ← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun ρ hρ => ?_
    obtain ⟨h0, h5⟩ := Finset.mem_filter.mp hρ
    obtain ⟨h1', -, -, -, hne⟩ := hS ρ h0
    have hb : 1 / 2 ≤ (ρ : ℂ).re := by
      have : 0 ≤ α / Real.log T := by positivity
      linarith
    have hN0 : 0 < normalDerivative (ρ : ℂ) := lt_of_le_of_ne (normalDerivative_nonneg hb) hne.symm
    have hlt : normalDerivative (ρ : ℂ) < B₀ := not_le.mp h5
    have hsq2 : normalDerivative (ρ : ℂ) ^ 2 ≤ 1 / (2 * J) := by
      rw [← hsq]
      exact pow_le_pow_left₀ hN0.le hlt.le 2
    have := one_div_le_one_div_of_le (by positivity) hsq2
    rw [one_div_one_div, one_div] at this
    exact this
  have hhalf : ((S.filter fun ρ : zetaZeroConfig.carrier => ¬ B₀ ≤ normalDerivative (ρ : ℂ)).card : ℝ) ≤
      S.card / 2 := by
    have h2 : J * (2 * (((S.filter fun ρ : zetaZeroConfig.carrier =>
        ¬ B₀ ≤ normalDerivative (ρ : ℂ)).card : ℕ) : ℝ)) ≤ J * S.card := by
      calc _ = 2 * J * (((S.filter fun ρ : zetaZeroConfig.carrier =>
            ¬ B₀ ≤ normalDerivative (ρ : ℂ)).card : ℕ) : ℝ) := by ring
        _ ≤ _ := hsmall
    have h3 := le_of_mul_le_mul_left h2 hJ0
    linarith
  have hsplitR : ((S.filter fun ρ : zetaZeroConfig.carrier => B₀ ≤ normalDerivative (ρ : ℂ)).card : ℝ) +
      ((S.filter fun ρ : zetaZeroConfig.carrier => ¬ B₀ ≤ normalDerivative (ρ : ℂ)).card : ℝ) = S.card := by
    exact_mod_cast hsplit
  rw [← hS₁] at hsplitR
  have hdouble : (S.card : ℝ) ≤ 2 * S₁.card := by linarith
  have hE0 := Real.exp_pos (-(2 * (1 - 3 * c) * α))
  have hrate : C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 =
      2 * C * J * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) := by
    rw [hsq]
    field_simp
  rw [hrate] at hcount
  have hR0 : 0 ≤ C * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2)) := by positivity
  nlinarith

/-! ### The mollified field -/

/-- A mollifier is outer: `|M(ρ)| exp ∫ P_ρ log |ζ| ≤ (∫ P_ρ |ζM|²)^{1/2}` for the Möbius polynomial `M` at a simple zero. -/
theorem norm_moebiusPoly_mul_exp_le_sqrt {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) (hre1 : ρ.re < 1)
    (hdz : deriv riemannZeta ρ ≠ 0) (X : ℕ) (hM : moebiusPoly X ρ ≠ 0) :
    ‖moebiusPoly X ρ‖ * Real.exp (∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖) ≤
      Real.sqrt (∫ u : ℝ, zeroPoisson ρ u * ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2) := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp at hre1
  have hδ : 0 < ρ.re - 1 / 2 := by linarith
  have hsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  -- integrability of the two logarithms
  obtain ⟨K, -, hK⟩ := _root_.RHTower.exists_norm_zetaEntire_le
  have hzero : _root_.RHTower.zetaEntire ρ = 0 := by
    rw [_root_.RHTower.zetaEntire_eq hρ1, hζ, mul_zero]
  have hdE := deriv_zetaEntire_of_zero hρ1 hζ
  have hmain := blaschke_poisson_le (E := _root_.RHTower.zetaEntire) _root_.RHTower.differentiable_zetaEntire
    hK hδ (γ := ρ.im) ∅ (by simp) (by simp) (by rw [offLinePoint_re_im]; exact hzero)
    (by rw [offLinePoint_re_im, hdE]; exact mul_ne_zero hsub hdz)
  obtain ⟨hintZ, -⟩ := integrable_and_integral_poisson_log_zeta hre hre1 hmain.1
  have hMdiff := differentiable_moebiusPoly X
  have hMgrow : ∀ z : ℂ, 1 / 2 ≤ z.re → ‖moebiusPoly X z‖ ≤ (X : ℝ) * (‖z‖ + 2) ^ 2 := fun z hz => by
    have h1 : ‖moebiusPoly X z‖ ≤ X := _root_.RHTower.norm_edPoly_mobCoeff_le X (by linarith)
    have h2 : (1 : ℝ) ≤ (‖z‖ + 2) ^ 2 := by nlinarith [norm_nonneg z]
    calc _ ≤ (X : ℝ) * 1 := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
  obtain ⟨hintM, hleM⟩ := integrable_and_log_norm_le_poisson hMdiff hMgrow hδ (γ := ρ.im)
    (by rw [offLinePoint_re_im]; exact hM)
  rw [offLinePoint_re_im] at hleM
  -- the logarithm of the product splits almost everywhere
  have hcountM : {u : ℝ | moebiusPoly X (linePoint u) = 0}.Countable :=
    (_root_.RHTower.countable_setOf_eq_zero_of_differentiable hMdiff hM).preimage_of_injOn
      linePoint_injective.injOn
  have hcountZ : {u : ℝ | _root_.RHTower.zetaEntire (linePoint u) = 0}.Countable :=
    (_root_.RHTower.countable_setOf_eq_zero_of_differentiable _root_.RHTower.differentiable_zetaEntire (x := 1) (by
      rw [_root_.RHTower.zetaEntire_eval_one]
      exact one_ne_zero)).preimage_of_injOn linePoint_injective.injOn
  have hne : ∀ᵐ u : ℝ, riemannZeta (linePoint u) * moebiusPoly X (linePoint u) ≠ 0 := by
    filter_upwards [hcountM.ae_notMem volume, hcountZ.ae_notMem volume] with u hu1 hu2
    refine mul_ne_zero (fun h => hu2 ?_) hu1
    show _root_.RHTower.zetaEntire (linePoint u) = 0
    rw [_root_.RHTower.zetaEntire_eq (linePoint_ne_one u), h, mul_zero]
  have hsum : Integrable fun u : ℝ => zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ +
      zeroPoisson ρ u * Real.log ‖moebiusPoly X (linePoint u)‖ := hintZ.add hintM
  have heq : (fun u : ℝ => zeroPoisson ρ u *
      Real.log ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖) =ᵐ[volume]
      fun u => zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ +
        zeroPoisson ρ u * Real.log ‖moebiusPoly X (linePoint u)‖ := by
    filter_upwards [hne] with u hu
    have h1 := left_ne_zero_of_mul hu
    have h2 := right_ne_zero_of_mul hu
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]
    ring
  have hintE : Integrable fun u : ℝ => zeroPoisson ρ u *
      Real.log ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ := hsum.congr heq.symm
  have hvalE : ∫ u : ℝ, zeroPoisson ρ u *
      Real.log ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ =
      (∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖) +
        ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖moebiusPoly X (linePoint u)‖ := by
    rw [integral_congr_ae heq, integral_add hintZ hintM]
  -- the second moment dominates
  have hcontζ : Continuous fun u : ℝ => riemannZeta (linePoint u) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (differentiableAt_riemannZeta (linePoint_ne_one u)).continuousAt.comp
      continuous_linePoint.continuousAt
  have hcontE : Continuous fun u : ℝ => riemannZeta (linePoint u) * moebiusPoly X (linePoint u) :=
    hcontζ.mul (hMdiff.continuous.comp continuous_linePoint)
  have hP0 := zeroPoisson_nonneg hre
  have hintQ : Integrable fun u : ℝ => zeroPoisson ρ u *
      ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ (2 : ℕ) := by
    have hb := ((integrable_zeroPoisson_mul_normSq_lineError hre X).const_mul 2).add
      ((integrable_zeroPoisson hre).const_mul 2)
    refine hb.mono' ?_ (Eventually.of_forall fun u => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact (continuous_halfPlanePoisson hδ |>.comp (continuous_id.sub continuous_const)).mul
        (hcontE.norm.pow 2)
    · have h0 := hP0 u
      have hE : riemannZeta (linePoint u) * moebiusPoly X (linePoint u) =
          lineError (moebiusPoly X) u + 1 := by
        unfold lineError
        ring
      have hn : ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2 ≤
          2 * ‖lineError (moebiusPoly X) u‖ ^ 2 + 2 := by
        rw [hE]
        have h1 := norm_add_le (lineError (moebiusPoly X) u) 1
        rw [norm_one] at h1
        have h2 := norm_nonneg (lineError (moebiusPoly X) u + 1)
        nlinarith [sq_nonneg (‖lineError (moebiusPoly X) u‖ - 1)]
      have hq : 0 ≤ zeroPoisson ρ u *
          ‖riemannZeta (linePoint u) * moebiusPoly X (linePoint u)‖ ^ 2 := by positivity
      rw [Real.norm_of_nonneg hq]
      show _ ≤ 2 * (zeroPoisson ρ u * ‖lineError (moebiusPoly X) u‖ ^ 2) + 2 * zeroPoisson ρ u
      nlinarith [mul_le_mul_of_nonneg_left hn h0]
  have hjensen := exp_mul_le_integral_poisson_norm_rpow (p := 2) hδ (γ := ρ.im)
    (E := fun u => riemannZeta (linePoint u) * moebiusPoly X (linePoint u)) hintE hne
    (by simpa only [Real.rpow_two] using hintQ)
  simp only [Real.rpow_two] at hjensen
  rw [hvalE] at hjensen
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖riemannZeta (linePoint u)‖ := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ∫ u : ℝ, zeroPoisson ρ u * Real.log ‖moebiusPoly X (linePoint u)‖ := ⟨_, rfl⟩
  rw [← hZ, ← hY] at hjensen
  rw [← hZ]
  have hleM' : Real.log ‖moebiusPoly X ρ‖ ≤ Y := by
    rw [hY]
    exact hleM
  refine Real.le_sqrt_of_sq_le ?_
  refine le_trans ?_ hjensen
  have hn0 : 0 < ‖moebiusPoly X ρ‖ := norm_pos_iff.mpr hM
  have h1 : ‖moebiusPoly X ρ‖ ≤ Real.exp Y := (Real.log_le_iff_le_exp hn0).mp hleM'
  have h2 : ‖moebiusPoly X ρ‖ * Real.exp Z ≤ Real.exp (Z + Y) := by
    rw [Real.exp_add, mul_comm]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have e : Real.exp (2 * (Z + Y)) = Real.exp (Z + Y) ^ 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  exact pow_le_pow_left₀ (by positivity) h2 2

/-- **The Möbius mollified field reads the same rate.** Fix `0 < c ≤ 1/28800`, `x = (1−3c)α`, `x ≤ (3/2) c log T`. For any lengths `X_ρ`, separated simple zeros of depth in `[α/L, (α+1)/L]` with
`M = moebiusPoly X_ρ` nonzero at `ρ` and `2b (|ρ − 1|/|ρ|) |ζ′(ρ) M(ρ)| ≥ B₀ (∫ P_ρ |ζM|²)^{1/2}`, `B₀ ≥ e^{−x/8}`, number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L³ T^{1/2}`. -/
theorem exists_card_zeros_with_normal_mollified_derivative_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 28800) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α B₀ : ℝ, 0 ≤ α →
      (1 - 3 * c) * α ≤ 3 / 2 * (c * Real.log T) →
      Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ (S : Finset zetaZeroConfig.carrier) (X : zetaZeroConfig.carrier → ℕ),
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧ 1 / 2 < (ρ : ℂ).re ∧
        deriv riemannZeta (ρ : ℂ) ≠ 0 ∧ moebiusPoly (X ρ) (ρ : ℂ) ≠ 0 ∧
        B₀ * Real.sqrt (∫ u : ℝ, zeroPoisson (ρ : ℂ) u *
            ‖riemannZeta (linePoint u) * moebiusPoly (X ρ) (linePoint u)‖ ^ 2) ≤
          2 * ((ρ : ℂ).re - 1 / 2) * (‖(ρ : ℂ) - 1‖ / ‖(ρ : ℂ)‖) *
            ‖deriv riemannZeta (ρ : ℂ) * moebiusPoly (X ρ) (ρ : ℂ)‖) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2)) := by
  obtain ⟨C, hC, hmain⟩ := exists_card_zeros_with_normal_derivative_le hv hsupp hv0 hI hc0 hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain] with T hT α B₀ hα hxL hB₀low hB₀1 S X hS hsep
  have hB₀ : 0 < B₀ := lt_of_lt_of_le (Real.exp_pos _) hB₀low
  refine hT α B₀ hα hxL hB₀low hB₀1 S (fun ρ hρ => ?_) hsep
  obtain ⟨h1, h2, h3, h4, hre, hdz, hM, hlow⟩ := hS ρ hρ
  refine ⟨h1, h2, h3, h4, ?_⟩
  obtain ⟨hζ, -, hre1⟩ : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hle := norm_moebiusPoly_mul_exp_le_sqrt hζ hre hre1 hdz (X ρ) hM
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫ u : ℝ, zeroPoisson (ρ : ℂ) u * Real.log ‖riemannZeta (linePoint u)‖ := ⟨_, rfl⟩
  rw [← hZ] at hle
  have hn0 : 0 < ‖moebiusPoly (X ρ) (ρ : ℂ)‖ := norm_pos_iff.mpr hM
  have hstep : B₀ * (‖moebiusPoly (X ρ) (ρ : ℂ)‖ * Real.exp Z) ≤
      2 * ((ρ : ℂ).re - 1 / 2) * (‖(ρ : ℂ) - 1‖ / ‖(ρ : ℂ)‖) *
        (‖deriv riemannZeta (ρ : ℂ)‖ * ‖moebiusPoly (X ρ) (ρ : ℂ)‖) := by
    rw [← norm_mul]
    exact (mul_le_mul_of_nonneg_left hle hB₀.le).trans hlow
  have hstep' : B₀ * Real.exp Z ≤
      2 * ((ρ : ℂ).re - 1 / 2) * (‖(ρ : ℂ) - 1‖ / ‖(ρ : ℂ)‖) * ‖deriv riemannZeta (ρ : ℂ)‖ := by
    refine le_of_mul_le_mul_right ?_ hn0
    calc _ = B₀ * (‖moebiusPoly (X ρ) (ρ : ℂ)‖ * Real.exp Z) := by ring
      _ ≤ _ := hstep
      _ = _ := by ring
  unfold normalDerivative
  rw [← hZ, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  exact hstep'

end GaloisForLFunctions.MultiscaleMollifiedZetaField
