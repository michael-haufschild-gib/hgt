import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Homogeneous Poisson modes for the finite polar defect

The integral is constructed, including absolute convergence and its exact axis
normalization. This is an analytic bridge; it does not assume or establish the
Mellin-residue representation of a cubic quotient.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace RHTower.WeilHigherDenominator

/-- Homogeneous boundary weight divided by the Euclidean Poisson denominator. -/
def polarKernel (ρ z : ℂ) (t : ℝ) : ℂ :=
  ((|t| : ℝ) : ℂ) ^ (-ρ) / (‖z - (t : ℂ)‖ : ℂ)

/-- The homogeneous quarter-eigenvalue Poisson integral. -/
def polarMode (ρ z : ℂ) : ℂ :=
  (Real.sqrt z.im : ℂ) * ∫ t : ℝ, polarKernel ρ z t

/-- Exact, nonvanishing axis normalization in the open critical strip. -/
def polarAxisFactor (ρ : ℂ) : ℂ :=
  Gamma ((1 - ρ) / 2) * Gamma (ρ / 2) / Gamma (1 / 2)

theorem polarAxisFactor_ne_zero {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    polarAxisFactor ρ ≠ 0 := by
  apply div_ne_zero
  · apply mul_ne_zero <;> apply Gamma_ne_zero_of_re_pos
    · norm_num [Complex.div_re, normSq_apply]
      linarith
    · norm_num [Complex.div_re, normSq_apply]
      linarith
  · apply Gamma_ne_zero_of_re_pos
    norm_num

private lemma norm_I_sub_real (t : ℝ) : ‖I - (t : ℂ)‖ = Real.sqrt (1 + t ^ 2) := by
  simp [Complex.norm_def, normSq_apply, sq, add_comm]

private lemma sqrt_inv_eq_cpow {u : ℝ} (hu : 0 ≤ u) :
    (Real.sqrt u : ℂ)⁻¹ = (u : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [cpow_neg, Real.sqrt_eq_rpow, ofReal_cpow hu]
  norm_num

private lemma square_beta_integrand (ρ : ℂ) {t : ℝ} (ht : 0 < t) :
    |2 * t| • (((t ^ 2 : ℝ) : ℂ) ^ ((1 - ρ) / 2 - 1) *
      (1 + ((t ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ))) =
      2 * polarKernel ρ I t := by
  have ht₀ : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hp : ((t : ℂ) ^ 2) ^ ((1 - ρ) / 2 - 1) = (t : ℂ) ^ (-ρ - 1) := by
    rw [← cpow_nat_mul' (n := 2) (by simp [arg_ofReal_of_nonneg ht.le, Real.pi_pos])
      (by simp [arg_ofReal_of_nonneg ht.le, Real.pi_pos.le])]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring_nf
  have hm : (t : ℂ) * (t : ℂ) ^ (-ρ - 1) = (t : ℂ) ^ (-ρ) := by
    conv_lhs => lhs; rw [← cpow_one (t : ℂ)]
    rw [← cpow_add _ _ ht₀]
    congr 1
    ring_nf
  rw [abs_of_pos (mul_pos (by norm_num) ht), Complex.real_smul, ofReal_mul,
    ofReal_ofNat, ofReal_pow, hp]
  simp only [polarKernel, abs_of_pos ht, norm_I_sub_real, div_eq_mul_inv]
  rw [sqrt_inv_eq_cpow (by positivity), ofReal_add, ofReal_one, ofReal_pow]
  calc
    _ = 2 * ((t : ℂ) * (t : ℂ) ^ (-ρ - 1)) *
        (1 + (t : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) := by ring_nf
    _ = _ := by rw [hm]; ring_nf

private lemma square_image_Ioi : (fun t : ℝ => t ^ 2) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact pow_pos (show 0 < t from ht) 2
  · intro hu
    exact ⟨Real.sqrt u, Real.sqrt_pos.mpr hu, Real.sq_sqrt hu.le⟩

/-- Half of the Gamma factor is the positive-axis Poisson integral. -/
theorem integral_polarKernel_Ioi {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    (∫ t in Ioi (0 : ℝ), polarKernel ρ I t) = polarAxisFactor ρ / 2 := by
  have hb := GaloisForLFunctions.HTGeometry.integral_halfLine_beta
    (w := (1 - ρ) / 2) (c := 1 / 2)
    (by norm_num [Complex.div_re, normSq_apply]; linarith)
    (by norm_num [Complex.div_re, normSq_apply]; linarith)
  have hj := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (f := fun t : ℝ => t ^ 2) (f' := fun t => 2 * t)
    (fun t _ => by simpa using (hasDerivAt_pow 2 t).hasDerivWithinAt)
    (show InjOn (fun t : ℝ => t ^ 2) (Ioi 0) from by
      intro t ht u hu htu
      dsimp at htu
      nlinarith [show 0 < t from ht, show 0 < u from hu])
    (fun v : ℝ => (v : ℂ) ^ ((1 - ρ) / 2 - 1) * (1 + (v : ℂ)) ^ (-(1 / 2 : ℂ)))
  rw [square_image_Ioi] at hj
  have heq : (∫ t in Ioi (0 : ℝ), |2 * t| •
      (((t ^ 2 : ℝ) : ℂ) ^ ((1 - ρ) / 2 - 1) *
        (1 + ((t ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ)))) =
      2 * ∫ t in Ioi (0 : ℝ), polarKernel ρ I t := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t ht => square_beta_integrand ρ ht
  have hc : (1 / 2 : ℂ) - (1 - ρ) / 2 = ρ / 2 := by ring
  rw [hc] at hb
  change _ = polarAxisFactor ρ at hb
  rw [hj, heq] at hb
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr
  simpa only [mul_comm] using hb

theorem integrableOn_polarKernel_Ioi {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    IntegrableOn (polarKernel ρ I) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_polarKernel_Ioi hρ₀ hρ₁]
  exact div_ne_zero (polarAxisFactor_ne_zero hρ₀ hρ₁) (by norm_num)

private lemma polarKernel_axis_neg (ρ : ℂ) (t : ℝ) :
    polarKernel ρ I (-t) = polarKernel ρ I t := by
  simp only [polarKernel, norm_I_sub_real, abs_neg, neg_sq]

private lemma integral_polarKernel_Iic (ρ : ℂ) :
    (∫ t in Iic (0 : ℝ), polarKernel ρ I t) =
      ∫ t in Ioi (0 : ℝ), polarKernel ρ I t := by
  simpa only [polarKernel_axis_neg, neg_zero] using
    integral_comp_neg_Iic 0 (polarKernel ρ I)

private lemma integrableOn_polarKernel_Iic {ρ : ℂ}
    (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    IntegrableOn (polarKernel ρ I) (Iic 0) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_polarKernel_Iic, integral_polarKernel_Ioi hρ₀ hρ₁]
  exact div_ne_zero (polarAxisFactor_ne_zero hρ₀ hρ₁) (by norm_num)

theorem integrable_polarKernel_axis {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    Integrable (polarKernel ρ I) := by
  have h := integrableOn_union.mpr
    ⟨integrableOn_polarKernel_Iic hρ₀ hρ₁, integrableOn_polarKernel_Ioi hρ₀ hρ₁⟩
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

theorem integral_polarKernel_axis {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    (∫ t : ℝ, polarKernel ρ I t) = polarAxisFactor ρ := by
  calc
    _ = (∫ t in Iic (0 : ℝ), polarKernel ρ I t) +
        ∫ t in Ioi (0 : ℝ), polarKernel ρ I t := by
      rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
        (integrableOn_polarKernel_Iic hρ₀ hρ₁) (integrableOn_polarKernel_Ioi hρ₀ hρ₁),
        Iic_union_Ioi, Measure.restrict_univ]
    _ = _ := by
      rw [integral_polarKernel_Iic, integral_polarKernel_Ioi hρ₀ hρ₁]
      ring

theorem measurable_polarKernel (ρ z : ℂ) : Measurable (polarKernel ρ z) := by
  have hw : Measurable (fun t : ℝ => ((|t| : ℝ) : ℂ) ^ (-ρ)) := by
    apply ContinuousOn.measurable_of_countable_compl (s := {0}ᶜ)
    · intro t ht
      have ht₀ : t ≠ 0 := by simpa using ht
      exact ((continuousAt_ofReal_cpow_const |t| (-ρ) (Or.inr (abs_ne_zero.mpr ht₀))).comp
        continuous_abs.continuousAt).continuousWithinAt
    · simpa only [compl_compl] using countable_singleton (0 : ℝ)
  exact hw.div (Complex.continuous_ofReal.comp
    (continuous_const.sub Complex.continuous_ofReal).norm).measurable

/-- One fixed integrable axis kernel dominates the kernel at every upper point. -/
theorem norm_polarKernel_le (ρ : ℂ) {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖polarKernel ρ z t‖ ≤ (1 + ‖I - z‖ / z.im) * ‖polarKernel ρ I t‖ := by
  have hy : z.im ≤ ‖z - (t : ℂ)‖ := by
    simpa using (le_abs_self (z - (t : ℂ)).im).trans (abs_im_le_norm _)
  have hd : 0 < ‖z - (t : ℂ)‖ := hz.trans_le hy
  have hi : 0 < ‖I - (t : ℂ)‖ := by rw [norm_I_sub_real]; positivity
  have htri : ‖I - (t : ℂ)‖ ≤ ‖z - (t : ℂ)‖ + ‖I - z‖ := by
    calc
      _ = ‖(z - (t : ℂ)) + (I - z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hmul := mul_le_mul_of_nonneg_left hy
    (div_nonneg (norm_nonneg (I - z)) hz.le)
  rw [div_mul_cancel₀ _ hz.ne'] at hmul
  have hbound : ‖I - (t : ℂ)‖ ≤ (1 + ‖I - z‖ / z.im) * ‖z - (t : ℂ)‖ := by
    nlinarith
  simp only [polarKernel, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  rw [← mul_div_assoc, div_le_div_iff₀ hd hi]
  calc
    _ ≤ ‖((|t| : ℝ) : ℂ) ^ (-ρ)‖ *
        ((1 + ‖I - z‖ / z.im) * ‖z - (t : ℂ)‖) :=
      mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = _ := by ring

/-- Absolute convergence uses exactly the open-strip bounds on the polar exponent. -/
theorem integrable_polarKernel {ρ z : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (hz : 0 < z.im) : Integrable (polarKernel ρ z) := by
  apply ((integrable_polarKernel_axis hρ₀ hρ₁).norm.const_mul
    (1 + ‖I - z‖ / z.im)).mono' (measurable_polarKernel ρ z).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_polarKernel_le ρ hz)

theorem polarKernel_dilate (ρ z : ℂ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    polarKernel ρ ((a : ℂ) * z) (a * t) =
      ((a : ℂ) ^ (-ρ) / (a : ℂ)) * polarKernel ρ z t := by
  have hn : ‖(a : ℂ) * z - ((a * t : ℝ) : ℂ)‖ = a * ‖z - (t : ℂ)‖ := by
    rw [ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  simp only [polarKernel, abs_mul, abs_of_pos ha, ofReal_mul,
    mul_cpow_ofReal_nonneg ha.le (abs_nonneg t)]
  rw [← ofReal_mul, hn, ofReal_mul]
  ring

theorem integral_polarKernel_dilate (ρ z : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, polarKernel ρ ((a : ℂ) * z) t) =
      (a : ℂ) ^ (-ρ) * ∫ t : ℝ, polarKernel ρ z t := by
  have hsub := Measure.integral_comp_mul_left (polarKernel ρ ((a : ℂ) * z)) a
  simp only [polarKernel_dilate ρ z ha, integral_const_mul,
    abs_of_pos (inv_pos.mpr ha), Complex.real_smul, ofReal_inv] at hsub
  have ha₀ : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  calc
    _ = (a : ℂ) * ((a : ℂ)⁻¹ * ∫ t : ℝ, polarKernel ρ ((a : ℂ) * z) t) := by
      rw [← mul_assoc, mul_inv_cancel₀ ha₀, one_mul]
    _ = _ := by rw [← hsub]; field_simp

/-- Exact positive-dilation covariance of the constructed mode. -/
theorem polarMode_dilate (ρ z : ℂ) {a : ℝ} (ha : 0 < a) :
    polarMode ρ ((a : ℂ) * z) = (a : ℂ) ^ (1 / 2 - ρ) * polarMode ρ z := by
  have ha₀ : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hs : (Real.sqrt a : ℂ) = (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow ha.le]
    norm_num
  simp only [polarMode, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    Real.sqrt_mul ha.le, ofReal_mul, integral_polarKernel_dilate ρ z ha]
  rw [hs, sub_eq_add_neg, cpow_add _ _ ha₀]
  ring

/-- No regularity or asymptotic premise: the actual integral has this axis value. -/
theorem polarMode_axis {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    {y : ℝ} (hy : 0 < y) :
    polarMode ρ ((y : ℂ) * I) = polarAxisFactor ρ * (y : ℂ) ^ (1 / 2 - ρ) := by
  rw [polarMode_dilate ρ I hy]
  simp only [polarMode, I_im, Real.sqrt_one, ofReal_one, one_mul,
    integral_polarKernel_axis hρ₀ hρ₁]
  ring

theorem polarKernel_reflect (ρ z : ℂ) (t : ℝ) :
    polarKernel ρ (-conj z) t = polarKernel ρ z (-t) := by
  have he : -conj z - (t : ℂ) = -conj (z - ((-t : ℝ) : ℂ)) := by
    simp [sub_eq_add_neg, add_comm]
  simp only [polarKernel, abs_neg, he, norm_neg, norm_conj]

/-- The mode is even in the horizontal coordinate. -/
theorem polarMode_reflect (ρ z : ℂ) : polarMode ρ (-conj z) = polarMode ρ z := by
  have hi : (∫ t : ℝ, polarKernel ρ z (-t)) = ∫ t : ℝ, polarKernel ρ z t := by
    simpa using Measure.integral_comp_mul_left (polarKernel ρ z) (-1)
  simp only [polarMode, neg_im, conj_im, neg_neg, polarKernel_reflect, hi]

/-- The mode normalized to have unit axial coefficient. -/
def normalizedPolarMode (ρ z : ℂ) : ℂ := polarMode ρ z / polarAxisFactor ρ

theorem normalizedPolarMode_axis {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    {y : ℝ} (hy : 0 < y) :
    normalizedPolarMode ρ ((y : ℂ) * I) = (y : ℂ) ^ (1 / 2 - ρ) := by
  simp only [normalizedPolarMode, polarMode_axis hρ₀ hρ₁ hy]
  exact mul_div_cancel_left₀ _ (polarAxisFactor_ne_zero hρ₀ hρ₁)

theorem polarMode_axis_ne_zero {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    {y : ℝ} (hy : 0 < y) : polarMode ρ ((y : ℂ) * I) ≠ 0 := by
  rw [polarMode_axis hρ₀ hρ₁ hy]
  exact mul_ne_zero (polarAxisFactor_ne_zero hρ₀ hρ₁)
    (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hy.ne')))

theorem polarAxisFactor_reflect (ρ : ℂ) : polarAxisFactor (1 - ρ) = polarAxisFactor ρ := by
  simp only [polarAxisFactor, sub_sub_cancel]
  rw [mul_comm]

/-- The leading boundary multiplier in the paper construction has no exceptional exponent. -/
theorem polarBoundaryFactor_ne_zero {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    (-2 : ℂ) / polarAxisFactor ρ ≠ 0 :=
  div_ne_zero (by norm_num) (polarAxisFactor_ne_zero hρ₀ hρ₁)

end RHTower.WeilHigherDenominator
