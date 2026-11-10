import GaloisForLFunctions.EulerFETransportTheory.PositiveContinuousPerturbationsOfTheRiemannPrimes
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import GaloisForLFunctions.HTGeometry.SchwartzWeightedHolder

/-!
# Integrable defects from continuous prime perturbations

On the critical line, reflection cancels the leading inverse-square term
of the continuous Euler multiplier. Its difference is inverse-cubic in
height. The elementary linear bound for zeta consequently gives an
inverse-square bound for the uncompleted functional-equation defect.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.EulerFETransportTheory

private theorem norm_exp_sub_exp_le_of_re_le (z w : ℂ) (M : ℝ)
    (hz : z.re ≤ M) (hw : w.re ≤ M) :
    ‖Complex.exp z - Complex.exp w‖ ≤ Real.exp M * ‖z - w‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Complex.hasDerivAt_exp u).hasDerivWithinAt)
    (fun u hu => by rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr hu)
    (convex_halfSpace_re_le M) hw hz

/-- The exponent is uniformly bounded throughout the right half-plane. -/
theorem norm_continuousEulerExponent_le (ε : ℝ≥0) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(ε : ℂ) / (s + 1) ^ 2‖ ≤ ε := by
  have hn : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith only [hs, h]
  rw [norm_div, norm_pow]
  have he : ‖(ε : ℂ)‖ = (ε : ℝ) := by
    change ‖((ε : ℝ) : ℂ)‖ = (ε : ℝ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ε.property]
  rw [he]
  have hsq : 1 ≤ ‖s + 1‖ ^ 2 := by nlinarith only [hn, sq_nonneg (‖s + 1‖ - 1)]
  apply (div_le_iff₀ (zero_lt_one.trans_le hsq)).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq ε.property

/-- The reflected inverse squares differ by an exactly inverse-cubic term. -/
theorem norm_continuousEulerExponent_sub_reflection (ε : ℝ≥0) {s : ℂ}
    (hs : s.re = 1 / 2) :
    ‖(ε : ℂ) / (s + 1) ^ 2 - (ε : ℂ) / (2 - s) ^ 2‖ =
      6 * ε * |s.im| / (9 / 4 + s.im ^ 2) ^ 2 := by
  have hz : s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num [hs] at h'
  have hw : 2 - s ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num [hs] at h'
  have hid : (ε : ℂ) / (s + 1) ^ 2 - (ε : ℂ) / (2 - s) ^ 2 =
      (ε : ℂ) * (3 - 6 * s) / ((s + 1) ^ 2 * (2 - s) ^ 2) := by
    field_simp [hz, hw]
    ring
  have hnum : (3 : ℂ) - 6 * s = (-6 * s.im : ℝ) * I := by
    apply Complex.ext <;> simp [hs] <;> ring
  have hden₁ : ‖s + 1‖ ^ 2 = 9 / 4 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero, hs]
    ring
  have hden₂ : ‖2 - s‖ ^ 2 = 9 / 4 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofNat_re, Complex.ofNat_im, zero_sub, hs]
    ring
  have he : ‖(ε : ℂ)‖ = (ε : ℝ) := by
    change ‖((ε : ℝ) : ℂ)‖ = (ε : ℝ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ε.property]
  rw [hid, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hden₁, hden₂,
    he, hnum, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul]
  norm_num
  ring

/-- Reflection gives one extra power of height beyond the individual multiplier bounds. -/
theorem norm_continuousEulerMultiplier_sub_reflection_le (ε : ℝ≥0) {s : ℂ}
    (hs : s.re = 1 / 2) :
    ‖Complex.exp ((ε : ℂ) / (s + 1) ^ 2) -
        Complex.exp ((ε : ℂ) / (2 - s) ^ 2)‖ ≤
      Real.exp ε * (6 * ε * |s.im| / (9 / 4 + s.im ^ 2) ^ 2) := by
  have hz := norm_continuousEulerExponent_le ε (s := s) (by rw [hs]; norm_num)
  have hw := norm_continuousEulerExponent_le ε (s := 1 - s)
    (by simp only [Complex.sub_re, Complex.one_re, hs]; norm_num)
  have hr : (1 : ℂ) - s + 1 = 2 - s := by ring
  rw [hr] at hw
  have h := norm_exp_sub_exp_le_of_re_le _ _ (ε : ℝ)
    ((Complex.re_le_norm _).trans hz) ((Complex.re_le_norm _).trans hw)
  rwa [norm_continuousEulerExponent_sub_reflection ε hs] at h

private theorem continuous_zeta_critical :
    Continuous fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + t * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hs : ((1 / 2 : ℂ) + t * I) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  exact (differentiableAt_riemannZeta hs).continuousAt.comp (by fun_prop)

/-- An unconditional global linear majorant on the critical line. -/
theorem exists_linear_bound_zeta_critical :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + t * I)‖ ≤ B * (1 + |t|) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    continuous_zeta_critical.continuousOn
  refine ⟨max B 4, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun t => ?_⟩
  by_cases ht : 2 ≤ |t|
  · have h := RHTower.norm_riemannZeta_le_of_re_pos (σ := 1 / 2)
      (by norm_num) (by norm_num) ht
    calc
      _ ≤ 4 * (1 + |t|) := by norm_num at h; linarith only [h]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · have ht' : t ∈ Icc (-2 : ℝ) 2 := by
      have ha := abs_lt.mp (lt_of_not_ge ht)
      exact ⟨ha.1.le, ha.2.le⟩
    calc
      _ ≤ B := hB t ht'
      _ ≤ max B 4 := le_max_left _ _
      _ ≤ max B 4 * (1 + |t|) := by
        have hm : 0 ≤ max B 4 := (by norm_num : (0 : ℝ) ≤ 4).trans (le_max_right _ _)
        nlinarith only [mul_nonneg hm (abs_nonneg t)]

/-- Uncompleted FE defect, parametrized as `s=1/2+2it`. -/
def continuousEulerDefect (ε : ℝ≥0) (t : ℝ) : ℂ :=
  let s : ℂ := 1 / 2 + (2 * t : ℝ) * I
  riemannZeta s * (Complex.exp ((ε : ℂ) / (s + 1) ^ 2) -
    Complex.exp ((ε : ℂ) / (2 - s) ^ 2))

theorem continuous_continuousEulerDefect (ε : ℝ≥0) : Continuous (continuousEulerDefect ε) := by
  have hζ : Continuous fun t : ℝ => riemannZeta ((1 / 2 : ℂ) + (2 * t : ℝ) * I) :=
    continuous_zeta_critical.comp (by fun_prop)
  have hz (t : ℝ) : (1 / 2 : ℂ) + (2 * t : ℝ) * I + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  have hw (t : ℝ) : (2 : ℂ) - ((1 / 2 : ℂ) + (2 * t : ℝ) * I) ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    norm_num at h'
  unfold continuousEulerDefect
  refine hζ.mul ((Complex.continuous_exp.comp ?_).sub (Complex.continuous_exp.comp ?_))
  · exact continuous_const.div (by fun_prop) (fun t => pow_ne_zero 2 (hz t))
  · exact continuous_const.div (by fun_prop) (fun t => pow_ne_zero 2 (hw t))

private theorem reflected_decay_ratio (y : ℝ) :
    (1 + |y|) * |y| / (9 / 4 + y ^ 2) ^ 2 ≤ 2 / (1 + y ^ 2) := by
  have hD : 0 < 1 + y ^ 2 := by positivity
  have hA : 0 < (9 / 4 : ℝ) + y ^ 2 := by positivity
  have hnum : (1 + |y|) * |y| ≤ 2 * (1 + y ^ 2) := by
    nlinarith only [sq_nonneg (|y| - 1), sq_abs y, sq_nonneg y]
  have hsq : (1 + y ^ 2) ^ 2 ≤ (9 / 4 + y ^ 2) ^ 2 := by
    nlinarith only [sq_nonneg y]
  apply (div_le_div_iff₀ (sq_pos_of_pos hA) hD).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hnum hD.le, hsq]

/-- One fixed majorant controls the whole positive deformation family. -/
theorem exists_uniform_continuousEulerDefect_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ≥0) (t : ℝ),
      ‖continuousEulerDefect ε t‖ ≤ C * ε * Real.exp ε / (1 + t ^ 2) := by
  obtain ⟨B, hB, hζ⟩ := exists_linear_bound_zeta_critical
  refine ⟨12 * B, by positivity, fun ε t => ?_⟩
  have hm := norm_continuousEulerMultiplier_sub_reflection_le ε
    (s := (1 / 2 : ℂ) + (2 * t : ℝ) * I) (by norm_num)
  have him : ((1 / 2 : ℂ) + (2 * t : ℝ) * I).im = 2 * t := by simp
  rw [him] at hm
  have hK : 0 ≤ 6 * B * (ε : ℝ) * Real.exp ε := by positivity
  calc
    ‖continuousEulerDefect ε t‖ ≤
        (B * (1 + |2 * t|)) *
          (Real.exp ε * (6 * ε * |2 * t| / (9 / 4 + (2 * t) ^ 2) ^ 2)) := by
      rw [continuousEulerDefect, norm_mul]
      exact mul_le_mul (hζ (2 * t)) hm (norm_nonneg _) (by positivity)
    _ = (6 * B * ε * Real.exp ε) *
        ((1 + |2 * t|) * |2 * t| / (9 / 4 + (2 * t) ^ 2) ^ 2) := by ring
    _ ≤ (6 * B * ε * Real.exp ε) * (2 / (1 + (2 * t) ^ 2)) :=
      mul_le_mul_of_nonneg_left (reflected_decay_ratio (2 * t)) hK
    _ = (12 * B) * ε * Real.exp ε / (1 + (2 * t) ^ 2) := by ring
    _ ≤ (12 * B) * ε * Real.exp ε / (1 + t ^ 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith only [sq_nonneg t]

/-- The uncompleted defect is integrable for every positive perturbation size. -/
theorem integrable_continuousEulerDefect (ε : ℝ≥0) : Integrable (continuousEulerDefect ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_continuousEulerDefect_bound
  apply (integrable_inv_one_add_sq.const_mul (C * ε * Real.exp ε)).mono'
    (continuous_continuousEulerDefect ε).aestronglyMeasurable
  exact Eventually.of_forall fun t => by simpa only [div_eq_mul_inv] using hbound ε t

/-- The same defect has finite square energy. -/
theorem memLp_continuousEulerDefect (ε : ℝ≥0) :
    MemLp (continuousEulerDefect ε) 2 (volume : Measure ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_continuousEulerDefect_bound
  apply (memLp_inv_one_add_sq.const_mul (C * ε * Real.exp ε)).mono
    (continuous_continuousEulerDefect ε).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simpa only [div_eq_mul_inv] using hbound ε t

#print axioms integrable_continuousEulerDefect
#print axioms memLp_continuousEulerDefect

end GaloisForLFunctions.EulerFETransportTheory
