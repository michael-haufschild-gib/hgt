import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Rational Poisson-kernel integrals on the line

The two integrals every Poisson computation on the half-plane reduces to:

`∫_ℝ dx/(a² + x²) = π/a`,   `∫_ℝ dx/((a² + x²)(b² + x²)) = π/(ab(a+b))`   for `a ≠ b`.

The first is the arctangent integral after the scaling `x ↦ x/a`; the second is partial fractions
against the first.  These are the elementary inputs behind the reproducing property of the Poisson
kernel, which is what turns an archimedean density into a value of the digamma function.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

theorem integrable_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    Integrable fun x : ℝ => ((a ^ 2 + x ^ 2)⁻¹) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hbase : Integrable fun x : ℝ => ((1 : ℝ) + (x / a) ^ 2)⁻¹ := by
    exact integrable_inv_one_add_sq.comp_div hane
  have hcongr : ∀ x : ℝ, (a ^ 2)⁻¹ * ((1 : ℝ) + (x / a) ^ 2)⁻¹ = (a ^ 2 + x ^ 2)⁻¹ := by
    intro x
    rw [← mul_inv]
    congr 1
    field_simp
  exact (hbase.const_mul ((a ^ 2)⁻¹)).congr (Filter.Eventually.of_forall hcongr)

/-- **The Poisson normalisation.** -/
theorem integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, ((a ^ 2 + x ^ 2)⁻¹)) = Real.pi / a := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hcongr : ∀ x : ℝ, (a ^ 2 + x ^ 2)⁻¹ = (a ^ 2)⁻¹ * ((1 : ℝ) + (x / a) ^ 2)⁻¹ := by
    intro x
    rw [← mul_inv]
    congr 1
    field_simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul]
  have hscale : (∫ x : ℝ, ((1 : ℝ) + (x / a) ^ 2)⁻¹) = |a| * ∫ y : ℝ, ((1 : ℝ) + y ^ 2)⁻¹ := by
    have h := MeasureTheory.Measure.integral_comp_div (fun u : ℝ => ((1 : ℝ) + u ^ 2)⁻¹) a
    simpa using h
  rw [hscale, integral_univ_inv_one_add_sq, abs_of_pos ha]
  field_simp

/-- **The product Poisson integral at distinct heights.** -/
theorem integral_inv_sq_add_sq_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (∫ x : ℝ, (((a ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))⁻¹))
      = Real.pi / (a * b * (a + b)) := by
  have hdiff : b ^ 2 - a ^ 2 ≠ 0 := by
    intro h0
    have hfac : (b - a) * (b + a) = 0 := by linarith [h0]
    rcases mul_eq_zero.1 hfac with h | h
    · exact hab (by linarith)
    · linarith
  have hcongr : ∀ x : ℝ, ((a ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))⁻¹
      = (b ^ 2 - a ^ 2)⁻¹ * ((a ^ 2 + x ^ 2)⁻¹ - (b ^ 2 + x ^ 2)⁻¹) := by
    intro x
    have h1 : (a ^ 2 + x ^ 2) ≠ 0 := by positivity
    have h2 : (b ^ 2 + x ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub (integrable_inv_sq_add_sq ha) (integrable_inv_sq_add_sq hb),
    integral_inv_sq_add_sq ha, integral_inv_sq_add_sq hb]
  have hane : a ≠ 0 := ne_of_gt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have habpos : a + b ≠ 0 := by positivity
  field_simp
  ring


theorem hasDerivAt_sq_add_sq {a : ℝ} (x : ℝ) :
    HasDerivAt (fun t : ℝ => a ^ 2 + t ^ 2) (2 * x) x := by
  have h : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  exact h.const_add (a ^ 2)

/-- The elementary antiderivative of the squared Poisson kernel. -/
theorem hasDerivAt_poissonSquareAntideriv {a : ℝ} (ha : 0 < a) (x : ℝ) :
    HasDerivAt (fun t : ℝ => t / (2 * a ^ 2 * (a ^ 2 + t ^ 2))
        + Real.arctan (t / a) / (2 * a ^ 3))
      (((a ^ 2 + x ^ 2) ^ 2)⁻¹) x := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hden : (2 * a ^ 2 * (a ^ 2 + x ^ 2)) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t / (2 * a ^ 2 * (a ^ 2 + t ^ 2)))
      ((1 * (2 * a ^ 2 * (a ^ 2 + x ^ 2)) - x * (2 * a ^ 2 * (2 * x)))
        / (2 * a ^ 2 * (a ^ 2 + x ^ 2)) ^ 2) x :=
    (hasDerivAt_id x).div
      (HasDerivAt.const_mul (2 * a ^ 2) (hasDerivAt_sq_add_sq (a := a) x)) hden
  have h2 : HasDerivAt (fun t : ℝ => Real.arctan (t / a) / (2 * a ^ 3))
      ((1 / (1 + (x / a) ^ 2) * (1 / a)) / (2 * a ^ 3)) x :=
    (((hasDerivAt_id x).div_const a).arctan).div_const (2 * a ^ 3)
  have h := h1.add h2
  refine h.congr_deriv ?_
  have h1pos : (1 : ℝ) + (x / a) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem continuous_inv_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    Continuous fun x : ℝ => (((a ^ 2 + x ^ 2) ^ 2)⁻¹) := by
  refine Continuous.inv₀ (by fun_prop) fun x => ?_
  have : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  positivity

theorem integrable_inv_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    Integrable fun x : ℝ => (((a ^ 2 + x ^ 2) ^ 2)⁻¹) := by
  refine ((integrable_inv_sq_add_sq ha).const_mul ((a ^ 2)⁻¹)).mono'
    (continuous_inv_sq_add_sq_sq ha).aestronglyMeasurable ?_
  filter_upwards with x
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have hle : (a ^ 2 + x ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
    have h1 : a ^ 2 ≤ a ^ 2 + x ^ 2 := by nlinarith [sq_nonneg x]
    simpa [one_div] using one_div_le_one_div_of_le ha2 h1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq, mul_inv]
  exact mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.mpr hpos))

/-- The Poisson profile vanishes at infinity in both directions. -/
theorem tendsto_div_sq_add_sq_cocompact {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun t : ℝ => t / (a ^ 2 + t ^ 2)) (Filter.cocompact ℝ) (nhds 0) := by
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖t‖) (Filter.cocompact ℝ) Filter.atTop :=
    tendsto_norm_cocompact_atTop
  have hinv : Filter.Tendsto (fun t : ℝ => ‖t‖⁻¹) (Filter.cocompact ℝ) (nhds 0) :=
    Filter.Tendsto.comp tendsto_inv_atTop_zero hnorm
  refine squeeze_zero_norm' ?_ hinv
  filter_upwards [hnorm.eventually_ge_atTop 1] with t ht
  have ht0 : (0 : ℝ) < |t| := by
    rw [Real.norm_eq_abs] at ht
    linarith
  have hpos : (0 : ℝ) < a ^ 2 + t ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, Real.norm_eq_abs, ← one_div,
    div_le_div_iff₀ hpos ht0]
  nlinarith [sq_abs t, sq_nonneg a]

/-- **The squared Poisson normalisation.** -/
theorem integral_inv_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, (((a ^ 2 + x ^ 2) ^ 2)⁻¹)) = Real.pi / (2 * a ^ 3) := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hcoc := tendsto_div_sq_add_sq_cocompact ha
  rw [cocompact_eq_atBot_atTop] at hcoc
  have hprofTop : Filter.Tendsto (fun t : ℝ => t / (2 * a ^ 2 * (a ^ 2 + t ^ 2)))
      Filter.atTop (nhds 0) := by
    have h := (hcoc.mono_left le_sup_right).const_mul ((2 * a ^ 2)⁻¹)
    rw [mul_zero] at h
    exact h.congr fun t => by
      rw [inv_mul_eq_div, div_div, mul_comm (a ^ 2 + t ^ 2) (2 * a ^ 2)]
  have hprofBot : Filter.Tendsto (fun t : ℝ => t / (2 * a ^ 2 * (a ^ 2 + t ^ 2)))
      Filter.atBot (nhds 0) := by
    have h := (hcoc.mono_left le_sup_left).const_mul ((2 * a ^ 2)⁻¹)
    rw [mul_zero] at h
    exact h.congr fun t => by
      rw [inv_mul_eq_div, div_div, mul_comm (a ^ 2 + t ^ 2) (2 * a ^ 2)]
  have harcTop : Filter.Tendsto (fun t : ℝ => Real.arctan (t / a) / (2 * a ^ 3))
      Filter.atTop (nhds ((Real.pi / 2) / (2 * a ^ 3))) := by
    have hdiv : Filter.Tendsto (fun t : ℝ => t / a) Filter.atTop Filter.atTop :=
      Filter.Tendsto.atTop_div_const ha Filter.tendsto_id
    have harc : Filter.Tendsto Real.arctan Filter.atTop (nhds (Real.pi / 2)) :=
      Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
    exact (harc.comp hdiv).div_const (2 * a ^ 3)
  have harcBot : Filter.Tendsto (fun t : ℝ => Real.arctan (t / a) / (2 * a ^ 3))
      Filter.atBot (nhds (-(Real.pi / 2) / (2 * a ^ 3))) := by
    have hdiv : Filter.Tendsto (fun t : ℝ => t / a) Filter.atBot Filter.atBot :=
      Filter.Tendsto.atBot_div_const ha Filter.tendsto_id
    have harc : Filter.Tendsto Real.arctan Filter.atBot (nhds (-(Real.pi / 2))) :=
      Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds
    exact (harc.comp hdiv).div_const (2 * a ^ 3)
  have hbot : Filter.Tendsto
      (fun t : ℝ => t / (2 * a ^ 2 * (a ^ 2 + t ^ 2)) + Real.arctan (t / a) / (2 * a ^ 3))
      Filter.atBot (nhds (-(Real.pi / 2) / (2 * a ^ 3))) := by
    have := hprofBot.add harcBot
    rwa [zero_add] at this
  have htop : Filter.Tendsto
      (fun t : ℝ => t / (2 * a ^ 2 * (a ^ 2 + t ^ 2)) + Real.arctan (t / a) / (2 * a ^ 3))
      Filter.atTop (nhds ((Real.pi / 2) / (2 * a ^ 3))) := by
    have := hprofTop.add harcTop
    rwa [zero_add] at this
  have h := MeasureTheory.integral_of_hasDerivAt_of_tendsto
    (hasDerivAt_poissonSquareAntideriv ha) (integrable_inv_sq_add_sq_sq ha) hbot htop
  rw [h]
  field_simp
  ring


theorem integrable_inv_sq_add_sq_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable fun x : ℝ => (((a ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))⁻¹) := by
  have hmeas : Continuous fun x : ℝ => (((a ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun x => ?_
    have h1 : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
    have h2 : (0 : ℝ) < b ^ 2 + x ^ 2 := by positivity
    positivity
  refine ((integrable_inv_sq_add_sq ha).const_mul ((b ^ 2)⁻¹)).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  have h1 : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have h2 : (0 : ℝ) < b ^ 2 + x ^ 2 := by positivity
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  have hle : (b ^ 2 + x ^ 2)⁻¹ ≤ (b ^ 2)⁻¹ := by
    have hstep : b ^ 2 ≤ b ^ 2 + x ^ 2 := by nlinarith [sq_nonneg x]
    simpa [one_div] using one_div_le_one_div_of_le hb2 hstep
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_inv, mul_comm ((a ^ 2 + x ^ 2)⁻¹)]
  exact mul_le_mul_of_nonneg_right hle (le_of_lt (inv_pos.mpr h1))

/-- **The product Poisson integral**, with no separation between the two heights. -/
theorem integral_inv_sq_add_sq_mul' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ, (((a ^ 2 + x ^ 2) * (b ^ 2 + x ^ 2))⁻¹))
      = Real.pi / (a * b * (a + b)) := by
  rcases eq_or_ne a b with rfl | hab
  · have hcongr : ∀ x : ℝ, ((a ^ 2 + x ^ 2) * (a ^ 2 + x ^ 2))⁻¹ = ((a ^ 2 + x ^ 2) ^ 2)⁻¹ := by
      intro x
      rw [← sq]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
      integral_inv_sq_add_sq_sq ha]
    have hane : a ≠ 0 := ne_of_gt ha
    field_simp
    ring
  · exact integral_inv_sq_add_sq_mul ha hb hab

end GaloisForLFunctions.HTGeometry
