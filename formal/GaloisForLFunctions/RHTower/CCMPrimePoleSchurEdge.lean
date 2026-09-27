import GaloisForLFunctions.RHTower.PrimeTransportPoleSchurNorm

/-!
# Complex edge energy in the pole-profile Schur bound

The weighted Schur defect is kept as a squared difference of complex values,
before taking any absolute value of a correlation. Integration identifies this
nonnegative edge energy with the two diagonal row contributions minus the
actual symmetric-translation pairing.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

def ccmPrimePoleRowDensity (a : SuzukiPositiveAperture) (h : ℝ)
    (f : SoninL2) (x : ℝ) : ℝ :=
  (centralInterval a.1).indicator primePoleProfile (x+h) / primePoleProfile x * ‖f x‖ ^ 2

def ccmPrimePoleEdgeDensity (a : SuzukiPositiveAperture) (h : ℝ)
    (f : SoninL2) (x : ℝ) : ℝ :=
  (centralInterval a.1 ∩ (fun y : ℝ => y+h) ⁻¹' centralInterval a.1).indicator
    (fun y => ‖(primePoleProfile y : ℂ) * f (y+h) -
      (primePoleProfile (y+h) : ℂ) * f y‖ ^ 2 /
        (primePoleProfile y * primePoleProfile (y+h))) x

def ccmPrimePoleEdgeEnergy (a : SuzukiPositiveAperture) (h : ℝ) (f : SoninL2) : ℝ :=
  ∫ x : ℝ, ccmPrimePoleEdgeDensity a h f x

private theorem complex_weighted_square (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (z w : ℂ) :
    ‖(u : ℂ) * z - (v : ℂ) * w‖ ^ 2 / (u*v) =
      u/v * ‖z‖ ^ 2 + v/u * ‖w‖ ^ 2 - 2 * (inner ℂ z w).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, RCLike.inner_apply, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

theorem ccmPrimePoleEdgeDensity_nonneg (a : SuzukiPositiveAperture)
    (h : ℝ) (f : SoninL2) (x : ℝ) : 0 ≤ ccmPrimePoleEdgeDensity a h f x := by
  unfold ccmPrimePoleEdgeDensity
  apply indicator_nonneg
  intro y _
  exact div_nonneg (sq_nonneg _) (mul_pos (primePoleProfile_pos _) (primePoleProfile_pos _)).le

private theorem pole_cutoff_le (a : SuzukiPositiveAperture) (y : ℝ) :
    (centralInterval a.1).indicator primePoleProfile y ≤ 2 * Real.exp (a.1/2) := by
  by_cases hy : y ∈ centralInterval a.1
  · rw [indicator_of_mem hy]
    have hp := Real.exp_le_exp.mpr (show y/2 ≤ a.1/2 by linarith [hy.2])
    have hm := Real.exp_le_exp.mpr (show -y/2 ≤ a.1/2 by linarith [hy.1])
    unfold primePoleProfile
    linarith
  · rw [indicator_of_notMem hy]
    positivity

theorem ccmPrimePoleRowDensity_bound (a : SuzukiPositiveAperture)
    (h : ℝ) (f : SoninL2) (x : ℝ) :
    0 ≤ ccmPrimePoleRowDensity a h f x ∧
      ccmPrimePoleRowDensity a h f x ≤ Real.exp (a.1/2) * ‖f x‖ ^ 2 := by
  have hp := primePoleProfile_pos x
  have hi : 0 ≤ (centralInterval a.1).indicator primePoleProfile (x+h) :=
    indicator_nonneg (fun y _ => (primePoleProfile_pos y).le) _
  constructor
  · exact mul_nonneg (div_nonneg hi hp.le) (sq_nonneg _)
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (div_le_iff₀ hp).mpr
    calc
      _ ≤ 2 * Real.exp (a.1/2) := pole_cutoff_le a (x+h)
      _ ≤ Real.exp (a.1/2) * primePoleProfile x := by
        nlinarith [two_le_primePoleProfile x, Real.exp_pos (a.1/2)]

theorem integrable_ccmPrimePoleRowDensity (a : SuzukiPositiveAperture)
    (h : ℝ) (f : SoninL2) : Integrable (ccmPrimePoleRowDensity a h f) := by
  have hnorm : Integrable (fun x : ℝ => ‖f x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hm : Measurable (ccmPrimePoleRowDensity a h f) := by
    unfold ccmPrimePoleRowDensity
    apply Measurable.mul
    · exact (((measurable_primePoleProfile.indicator (measurableSet_centralInterval a.1)).comp
        (measurable_id.add_const h)).div measurable_primePoleProfile)
    · exact (Lp.stronglyMeasurable f).measurable.norm.pow_const 2
  refine (hnorm.const_mul (Real.exp (a.1/2))).mono' hm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (ccmPrimePoleRowDensity_bound a h f x).1]
  exact (ccmPrimePoleRowDensity_bound a h f x).2

private theorem translation_ae (h : ℝ) (f : SoninL2) :
    (logTranslationCLM h f : ℝ → ℂ) =ᵐ[volume] fun x => f (x+h) :=
  (Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)).trans (Eventually.of_forall fun _ => rfl)

private theorem support_ae (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x : ℝ, x ∉ centralInterval a.1 → f.1 x = 0 := by
  have h := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at h
  filter_upwards [h] with x hx hn
  rw [hx, indicator_of_notMem hn]

theorem ccmPrimePoleEdgeDensity_eq_rows_sub_pair_ae (a : SuzukiPositiveAperture)
    (h : ℝ) (f : suzukiApertureHilbert a) :
    ccmPrimePoleEdgeDensity a h f.1 =ᵐ[volume] fun x =>
      ccmPrimePoleRowDensity a h f.1 x + ccmPrimePoleRowDensity a (-h) f.1 (x+h) -
        2 * (inner ℂ (logTranslationCLM h f.1 x) (f.1 x)).re := by
  have hz := support_ae a f
  have hzt := (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae.eventually hz
  filter_upwards [hz, hzt, translation_ae h f.1] with x hz hzt ht
  change (x+h ∉ centralInterval a.1 → f.1 (x+h) = 0) at hzt
  rw [ht]
  unfold ccmPrimePoleEdgeDensity ccmPrimePoleRowDensity
  rw [show x+h + -h = x by ring]
  by_cases hx : x ∈ centralInterval a.1 <;>
    by_cases hy : x+h ∈ centralInterval a.1
  · rw [indicator_of_mem (show x ∈ centralInterval a.1 ∩
        (fun y : ℝ => y+h) ⁻¹' centralInterval a.1 from ⟨hx,hy⟩),
      indicator_of_mem hx, indicator_of_mem hy,
      complex_weighted_square _ _ (primePoleProfile_pos x) (primePoleProfile_pos (x+h))]
    ring
  · simp [hx, hy, hzt hy]
  · simp [hx, hy, hz hx]
  · simp [hx, hy, hz hx, hzt hy]

theorem integrable_ccmPrimePoleEdgeDensity (a : SuzukiPositiveAperture)
    (h : ℝ) (f : suzukiApertureHilbert a) :
    Integrable (ccmPrimePoleEdgeDensity a h f.1) := by
  have hrow := integrable_ccmPrimePoleRowDensity a h f.1
  have hshift := (measurePreserving_add_right volume h).integrable_comp_of_integrable
    (integrable_ccmPrimePoleRowDensity a (-h) f.1)
  have hinner := (L2.integrable_inner (𝕜 := ℂ) (logTranslationCLM h f.1) f.1).re
  exact ((hrow.add hshift).sub (hinner.const_mul 2)).congr
    (ccmPrimePoleEdgeDensity_eq_rows_sub_pair_ae a h f).symm

theorem ccmPrimePoleEdgeEnergy_eq_rows_sub_pair (a : SuzukiPositiveAperture)
    (h : ℝ) (f : suzukiApertureHilbert a) :
    ccmPrimePoleEdgeEnergy a h f.1 =
      (∫ x : ℝ, ccmPrimePoleRowDensity a h f.1 x) +
      (∫ x : ℝ, ccmPrimePoleRowDensity a (-h) f.1 x) -
        2 * (inner ℂ (logTranslationCLM h f.1) f.1).re := by
  have hrow := integrable_ccmPrimePoleRowDensity a h f.1
  have hshift := (measurePreserving_add_right volume h).integrable_comp_of_integrable
    (integrable_ccmPrimePoleRowDensity a (-h) f.1)
  have hinner := (L2.integrable_inner (𝕜 := ℂ) (logTranslationCLM h f.1) f.1).re
  change Integrable (fun x : ℝ => (inner ℂ (logTranslationCLM h f.1 x) (f.1 x)).re) at hinner
  change Integrable (fun x : ℝ => ccmPrimePoleRowDensity a (-h) f.1 (x+h)) at hshift
  have hboth : Integrable (fun x : ℝ => ccmPrimePoleRowDensity a h f.1 x +
      ccmPrimePoleRowDensity a (-h) f.1 (x+h)) := hrow.add hshift
  unfold ccmPrimePoleEdgeEnergy
  rw [integral_congr_ae (ccmPrimePoleEdgeDensity_eq_rows_sub_pair_ae a h f),
    integral_sub hboth (hinner.const_mul 2), integral_add hrow hshift,
    integral_add_right_eq_self, integral_const_mul]
  rw [L2.inner_def]
  have hi := integral_re (L2.integrable_inner (𝕜 := ℂ) (logTranslationCLM h f.1) f.1)
  change (∫ x : ℝ, (inner ℂ (logTranslationCLM h f.1 x) (f.1 x)).re) =
    (∫ x : ℝ, inner ℂ (logTranslationCLM h f.1 x) (f.1 x)).re at hi
  rw [hi]

theorem ccmPrimePoleEdgeEnergy_nonneg (a : SuzukiPositiveAperture)
    (h : ℝ) (f : SoninL2) : 0 ≤ ccmPrimePoleEdgeEnergy a h f :=
  integral_nonneg (ccmPrimePoleEdgeDensity_nonneg a h f)

end RHTower
