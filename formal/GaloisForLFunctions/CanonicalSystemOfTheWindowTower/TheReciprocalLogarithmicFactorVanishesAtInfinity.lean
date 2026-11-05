import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFactorHasItsReflectionIdentity

/-!
# Uniform decay of the reciprocal logarithmic factor

The Poisson formula gives an angular upper bound by the logarithmic symbol.
A fixed interval of positive Poisson mass supplies a uniform lower bound in
the right half-plane. Reflection and the real part of the logarithmic symbol
control the left half-plane. Together they force the reciprocal factor to
vanish at infinity uniformly over all nonreal directions.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower

/-- An elementary comparison of the logarithmic symbol at two scales. -/
theorem positiveLogarithmicSymbol_le_mul {R : ℝ} (hR : 0 < R) (t : ℝ) :
    positiveLogarithmicSymbol t ≤ positiveLogarithmicSymbol R * (1 + t ^ 2 / R ^ 2) := by
  let d : ℝ := t ^ 2 / R ^ 2
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have he : R ^ 2 * d = t ^ 2 := by dsimp only [d]; field_simp
  have hp : 1 + t ^ 2 ≤ (1 + R ^ 2) * (1 + d) := by
    nlinarith only [he, hd, sq_nonneg R]
  have hl := Real.log_le_log (by positivity : 0 < 1 + t ^ 2) hp
  rw [Real.log_mul (by positivity : (1 + R ^ 2 : ℝ) ≠ 0)
    (by positivity : (1 + d : ℝ) ≠ 0)] at hl
  have hdlog := Real.log_le_sub_one_of_pos (show 0 < 1 + d by positivity)
  have hs : positiveLogarithmicSymbol t ≤ positiveLogarithmicSymbol R + d / 2 := by
    unfold positiveLogarithmicSymbol
    linarith only [hl, hdlog]
  have hm := mul_le_mul_of_nonneg_right (one_le_positiveLogarithmicSymbol R) hd
  calc
    _ ≤ positiveLogarithmicSymbol R + d / 2 := hs
    _ ≤ positiveLogarithmicSymbol R + positiveLogarithmicSymbol R * d := by
      linarith only [hd, hm]
    _ = _ := by dsimp only [d]; ring

private theorem integrable_log_sq_poisson :
    Integrable (fun u : ℝ => Real.log (1 + u ^ 2) / (1 + u ^ 2)) := by
  apply (integrable_logFactorMajorant.sub integrable_inv_one_add_sq).congr
  filter_upwards with u
  simp only [Pi.sub_apply, logFactorMajorant]
  ring

/-- A finite universal constant controlling the modulus of the logarithmic factor. -/
def logarithmicFactorGrowthConstant : ℝ :=
  Real.exp (Real.log 2 + (1 / Real.pi) * ∫ u : ℝ, Real.log (1 + u ^ 2) / (1 + u ^ 2))

theorem logarithmicFactorGrowthConstant_pos : 0 < logarithmicFactorGrowthConstant :=
  Real.exp_pos _

private theorem log_symbol_affine_norm_bound {z : ℂ} (hz : 0 < z.re) (u : ℝ) :
    Real.log (positiveLogarithmicSymbol (z.im + z.re * u)) ≤
      Real.log (positiveLogarithmicSymbol ‖z‖) + Real.log 2 + Real.log (1 + u ^ 2) := by
  have hR : 0 < ‖z‖ := hz.trans_le (Complex.re_le_norm z)
  have hsq : (z.im + z.re * u) ^ 2 ≤ ‖z‖ ^ 2 * (1 + u ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [sq_nonneg (z.im * u - z.re)]
  have hd : (z.im + z.re * u) ^ 2 / ‖z‖ ^ 2 ≤ 1 + u ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hR)).mpr (by nlinarith only [hsq])
  have hfac : 1 + (z.im + z.re * u) ^ 2 / ‖z‖ ^ 2 ≤ 2 * (1 + u ^ 2) := by
    nlinarith only [hd, sq_nonneg u]
  have hs := (positiveLogarithmicSymbol_le_mul hR (z.im + z.re * u)).trans
    (mul_le_mul_of_nonneg_left hfac (zero_le_one.trans (one_le_positiveLogarithmicSymbol ‖z‖)))
  have hl := Real.log_le_log (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol _)) hs
  rw [Real.log_mul (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol ‖z‖)).ne'
    (by positivity : (2 * (1 + u ^ 2) : ℝ) ≠ 0),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (1 + u ^ 2 : ℝ) ≠ 0)] at hl
  simpa only [add_assoc] using hl

/-- The factor grows at most like the square root of the logarithmic symbol, uniformly in angle. -/
theorem complexLogReferenceFactor_norm_sq_le {z : ℂ} (hz : 0 < z.re) :
    ‖complexLogReferenceFactor z‖ ^ 2 ≤
      logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ := by
  let L : ℝ := Real.log (positiveLogarithmicSymbol ‖z‖) + Real.log 2
  let g : ℝ → ℝ := fun u => Real.log (positiveLogarithmicSymbol (z.im + z.re * u)) / (1 + u ^ 2)
  let h : ℝ → ℝ := fun u => L * (1 + u ^ 2)⁻¹ + Real.log (1 + u ^ 2) / (1 + u ^ 2)
  have hgi : Integrable g := integrable_affine_logarithmic_poisson z.re z.im
  have hhi : Integrable h := (integrable_inv_one_add_sq.const_mul L).add integrable_log_sq_poisson
  have hle : ∀ u, g u ≤ h u := by
    intro u
    have hl := div_le_div_of_nonneg_right (log_symbol_affine_norm_bound hz u)
      (show 0 ≤ 1 + u ^ 2 by positivity)
    dsimp only [g, h]
    calc
      _ ≤ (L + Real.log (1 + u ^ 2)) / (1 + u ^ 2) := hl
      _ = _ := by ring
  have hi := integral_mono hgi hhi hle
  have he : (∫ u : ℝ, h u) = L * Real.pi +
      ∫ u : ℝ, Real.log (1 + u ^ 2) / (1 + u ^ 2) := by
    rw [show h = _ from rfl, integral_add (integrable_inv_one_add_sq.const_mul L)
      integrable_log_sq_poisson, integral_const_mul, integral_univ_inv_one_add_sq]
  rw [he] at hi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hscale := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / Real.pi by positivity)
  have hval : (1 / Real.pi) * (L * Real.pi + ∫ u : ℝ, Real.log (1 + u ^ 2) / (1 + u ^ 2)) =
      Real.log (positiveLogarithmicSymbol ‖z‖) + (Real.log 2 +
        (1 / Real.pi) * ∫ u : ℝ, Real.log (1 + u ^ 2) / (1 + u ^ 2)) := by
    dsimp only [L]
    field_simp
    ring
  rw [hval] at hscale
  rw [complexLogReferenceFactor_norm_sq hz]
  calc
    _ ≤ Real.exp (Real.log (positiveLogarithmicSymbol ‖z‖) + (Real.log 2 +
        (1 / Real.pi) * ∫ u : ℝ, Real.log (1 + u ^ 2) / (1 + u ^ 2))) :=
      Real.exp_le_exp.mpr hscale
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol ‖z‖))]
      exact mul_comm _ _

private theorem positiveLogarithmicSymbol_mono_nonneg {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    positiveLogarithmicSymbol s ≤ positiveLogarithmicSymbol t := by
  have hsq : s ^ 2 ≤ t ^ 2 := by nlinarith only [hs, hst]
  have hl := Real.log_le_log (by positivity : 0 < 1 + s ^ 2) (add_le_add (le_refl 1) hsq)
  unfold positiveLogarithmicSymbol
  linarith only [hl]

#print axioms complexLogReferenceFactor_norm_sq_le

private theorem complexLogReferenceFactor_norm_sq_lower_upper {z : ℂ}
    (hz : 0 < z.re) (hy : 0 ≤ z.im) :
    Real.exp (Real.log (positiveLogarithmicSymbol ‖z‖) / (5 * Real.pi)) ≤
      ‖complexLogReferenceFactor z‖ ^ 2 := by
  let L : ℝ := Real.log (positiveLogarithmicSymbol ‖z‖)
  let g : ℝ → ℝ := fun u => Real.log (positiveLogarithmicSymbol (z.im + z.re * u)) / (1 + u ^ 2)
  have hL : 0 ≤ L := log_positiveLogarithmicSymbol_nonneg ‖z‖
  have hg : Integrable g := integrable_affine_logarithmic_poisson z.re z.im
  have hgn : ∀ u, 0 ≤ g u := fun u =>
    div_nonneg (log_positiveLogarithmicSymbol_nonneg _) (by positivity)
  have hlow : ∀ u ∈ Icc (1 : ℝ) 2, L / 5 ≤ g u := by
    intro u hu
    have hR : ‖z‖ ≤ z.im + z.re * u := by
      have hn := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hz, abs_of_nonneg hy] at hn
      have hm := mul_le_mul_of_nonneg_left hu.1 hz.le
      nlinarith only [hn, hm]
    have hlog : L ≤ Real.log (positiveLogarithmicSymbol (z.im + z.re * u)) :=
      Real.log_le_log (zero_lt_one.trans_le (one_le_positiveLogarithmicSymbol ‖z‖))
        (positiveLogarithmicSymbol_mono_nonneg (norm_nonneg _) hR)
    have hden : 1 + u ^ 2 ≤ 5 := by nlinarith only [hu.1, hu.2]
    have hm := mul_le_mul_of_nonneg_left hden hL
    dsimp only [g]
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) (by positivity)).mpr
    nlinarith only [hm, hlog]
  have hc : IntegrableOn (fun _ : ℝ => L / 5) (Icc (1 : ℝ) 2) :=
    continuous_const.integrableOn_Icc
  have hi := setIntegral_mono_on hc hg.integrableOn measurableSet_Icc hlow
  have hconst : (∫ _ : ℝ in Icc (1 : ℝ) 2, L / 5) = L / 5 := by
    norm_num
  rw [hconst] at hi
  have hi' : L / 5 ≤ ∫ u : ℝ, g u :=
    hi.trans (setIntegral_le_integral hg (Eventually.of_forall hgn))
  rw [complexLogReferenceFactor_norm_sq hz]
  apply Real.exp_le_exp.mpr
  calc
    _ = (1 / Real.pi) * (L / 5) := by dsimp only [L]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hi' (by positivity : 0 ≤ 1 / Real.pi)

/-- A fixed positive mass of the Poisson kernel forces uniform growth in the right half-plane. -/
theorem complexLogReferenceFactor_norm_sq_lower {z : ℂ} (hz : 0 < z.re) :
    Real.exp (Real.log (positiveLogarithmicSymbol ‖z‖) / (5 * Real.pi)) ≤
      ‖complexLogReferenceFactor z‖ ^ 2 := by
  by_cases hy : 0 ≤ z.im
  · exact complexLogReferenceFactor_norm_sq_lower_upper hz hy
  · have hc : 0 < ((starRingEnd ℂ) z).re := by simpa using hz
    have hi : 0 ≤ ((starRingEnd ℂ) z).im := by
      simp only [Complex.conj_im]
      linarith only [lt_of_not_ge hy]
    have h := complexLogReferenceFactor_norm_sq_lower_upper hc hi
    rw [complexLogReferenceFactor_conj (Or.inl hz)] at h
    simpa only [Complex.norm_conj] using h

theorem one_le_norm_complexLogReferenceFactor {z : ℂ} (hz : 0 < z.re) :
    1 ≤ ‖complexLogReferenceFactor z‖ := by
  have he : 1 ≤ Real.exp (Real.log (positiveLogarithmicSymbol ‖z‖) / (5 * Real.pi)) :=
    Real.one_le_exp (div_nonneg (log_positiveLogarithmicSymbol_nonneg _) (by positivity))
  have hs := he.trans (complexLogReferenceFactor_norm_sq_lower hz)
  nlinarith only [hs, norm_nonneg (complexLogReferenceFactor z)]

#print axioms complexLogReferenceFactor_norm_sq_lower

private theorem log_le_positiveLogarithmicSymbol {r : ℝ} (hr : 0 < r) :
    Real.log r ≤ positiveLogarithmicSymbol r := by
  have hl := Real.log_le_log (sq_pos_of_pos hr)
    (show r ^ 2 ≤ 1 + r ^ 2 by linarith)
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  unfold positiveLogarithmicSymbol
  linarith only [hl]

theorem tendsto_positiveLogarithmicSymbol_atTop :
    Tendsto positiveLogarithmicSymbol atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro B
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop B, eventually_gt_atTop (0 : ℝ)]
    with r hB hr
  exact hB.trans (log_le_positiveLogarithmicSymbol hr)

private theorem tendsto_log_factor_reciprocal_majorant :
    Tendsto (fun r : ℝ => Real.sqrt (Real.exp
      (-(Real.log (positiveLogarithmicSymbol r) / (5 * Real.pi))))) atTop (nhds 0) := by
  have hl := Real.tendsto_log_atTop.comp tendsto_positiveLogarithmicSymbol_atTop
  have hs : Tendsto (fun r : ℝ => Real.log (positiveLogarithmicSymbol r) / (5 * Real.pi))
      atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro B
    filter_upwards [hl.eventually_ge_atTop (B * (5 * Real.pi))] with r hr
    exact (le_div_iff₀ (by positivity : 0 < 5 * Real.pi)).mpr hr
  have hn := tendsto_neg_atTop_atBot.comp hs
  have he := Real.tendsto_exp_atBot.comp hn
  simpa only [Function.comp_def, Real.sqrt_zero] using!
    Real.continuous_sqrt.continuousAt.tendsto.comp he

private theorem inv_complexLogReferenceFactor_norm_le {z : ℂ} (hz : 0 < z.re) :
    ‖(complexLogReferenceFactor z)⁻¹‖ ≤ Real.sqrt (Real.exp
      (-(Real.log (positiveLogarithmicSymbol ‖z‖) / (5 * Real.pi)))) := by
  have hs := one_div_le_one_div_of_le
    (Real.exp_pos (Real.log (positiveLogarithmicSymbol ‖z‖) / (5 * Real.pi)))
    (complexLogReferenceFactor_norm_sq_lower hz)
  have he : ‖(complexLogReferenceFactor z)⁻¹‖ ^ 2 ≤
      Real.exp (-(Real.log (positiveLogarithmicSymbol ‖z‖) / (5 * Real.pi))) := by
    simpa only [one_div, norm_inv, inv_pow, Real.exp_neg] using hs
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt he

/-- The reciprocal factor vanishes uniformly at infinity inside the right half-plane. -/
theorem tendsto_inv_complexLogReferenceFactor_right :
    Tendsto (fun z : ℂ => (complexLogReferenceFactor z)⁻¹)
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}) (nhds 0) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}) atTop :=
    tendsto_norm_cocompact_atTop.mono_left inf_le_left
  have hb := tendsto_log_factor_reciprocal_majorant.comp hn
  apply squeeze_zero_norm' _ hb
  have hr : ∀ᶠ z in cocompact ℂ ⊓ 𝓟 {z : ℂ | 0 < z.re}, 0 < z.re :=
    (Filter.eventually_principal.mpr (fun z hz => hz)).filter_mono inf_le_right
  filter_upwards [hr] with z hz
  exact inv_complexLogReferenceFactor_norm_le hz

#print axioms tendsto_inv_complexLogReferenceFactor_right

private theorem one_le_logarithmicFactorGrowthConstant : 1 ≤ logarithmicFactorGrowthConstant := by
  apply Real.one_le_exp
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : 0 ≤ ∫ u : ℝ, Real.log (1 + u ^ 2) / (1 + u ^ 2) := by
    apply integral_nonneg
    intro u
    exact div_nonneg (Real.log_nonneg (by nlinarith only [sq_nonneg u])) (by positivity)
  exact add_nonneg hl (mul_nonneg (by positivity) hi)

/-- The angular upper bound includes the imaginary boundary away from zero. -/
theorem complexLogReferenceFactor_norm_sq_le_closed {z : ℂ}
    (hz : 0 ≤ z.re) (hi : z.im ≠ 0) :
    ‖complexLogReferenceFactor z‖ ^ 2 ≤
      logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ := by
  rcases eq_or_lt_of_le hz with hr | hr
  · have hzre : z.re = 0 := hr.symm
    have he : z = (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hzre]
    have hs : positiveLogarithmicSymbol ‖z‖ = positiveLogarithmicSymbol z.im := by
      unfold positiveLogarithmicSymbol
      rw [Complex.sq_norm, Complex.normSq_apply, hzre, zero_mul, zero_add, ← pow_two]
    rw [he, complexLogReferenceFactor_imaginary_norm_sq hi, ← he, hs]
    exact le_mul_of_one_le_left (zero_le_one.trans (one_le_positiveLogarithmicSymbol _))
      one_le_logarithmicFactorGrowthConstant
  · exact complexLogReferenceFactor_norm_sq_le hr

/-- Reflection expresses the reciprocal factor through the opposite half-plane. -/
theorem inv_complexLogReferenceFactor_eq {z : ℂ} (hz : z.im ≠ 0) :
    (complexLogReferenceFactor z)⁻¹ =
      complexLogReferenceFactor (-z) / logarithmicLaplaceSymbol (-z ^ 2) := by
  have he : complexLogReferenceFactor z * complexLogReferenceFactor (-z) =
      logarithmicLaplaceSymbol (-z ^ 2) := by
    simpa only [logarithmicLaplaceSymbol, sub_eq_add_neg] using complexLogReferenceFactor_reflection hz
  rw [← he]
  field_simp [complexLogReferenceFactor_ne_zero z, complexLogReferenceFactor_ne_zero (-z)]

private theorem logarithmic_reflected_symbol_norm_lower {z : ℂ} (hz : 2 ≤ ‖z‖) :
    Real.log ‖z‖ / 2 ≤ ‖logarithmicLaplaceSymbol (-z ^ 2)‖ := by
  have hr : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hz
  have hrev : ‖z‖ ^ 2 - 1 ≤ ‖1 - z ^ 2‖ := by
    have h := norm_sub_norm_le (z ^ 2) (1 : ℂ)
    rw [norm_pow, norm_one, norm_sub_rev] at h
    exact h
  have hnorm : ‖z‖ ≤ ‖1 - z ^ 2‖ := by nlinarith only [hz, hrev]
  have hlog := Real.log_le_log hr hnorm
  have hre : (logarithmicLaplaceSymbol (-z ^ 2)).re =
      1 + (1 / 2 : ℝ) * Real.log ‖1 - z ^ 2‖ := by
    simp only [logarithmicLaplaceSymbol, Complex.add_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.log_re, ← sub_eq_add_neg]
  have hle := Complex.re_le_norm (logarithmicLaplaceSymbol (-z ^ 2))
  rw [hre] at hle
  linarith only [hle, hlog]

private theorem inv_complexLogReferenceFactor_norm_le_left {z : ℂ}
    (hz : z.re ≤ 0) (hi : z.im ≠ 0) (hR : 2 ≤ ‖z‖) :
    ‖(complexLogReferenceFactor z)⁻¹‖ ≤
      Real.sqrt (logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ /
        (Real.log ‖z‖ / 2) ^ 2) := by
  have hn : 0 ≤ (-z).re := by simpa only [Complex.neg_re] using neg_nonneg.mpr hz
  have hin : (-z).im ≠ 0 := by simpa only [Complex.neg_im, neg_ne_zero] using hi
  have hnum := complexLogReferenceFactor_norm_sq_le_closed hn hin
  rw [norm_neg] at hnum
  have hl : 0 < Real.log ‖z‖ := Real.log_pos (lt_of_lt_of_le (by norm_num) hR)
  have hd := logarithmic_reflected_symbol_norm_lower hR
  have hden : (Real.log ‖z‖ / 2) ^ 2 ≤ ‖logarithmicLaplaceSymbol (-z ^ 2)‖ ^ 2 := by
    nlinarith only [hd, norm_nonneg (logarithmicLaplaceSymbol (-z ^ 2)), hl]
  have hs : ‖(complexLogReferenceFactor z)⁻¹‖ ^ 2 ≤
      logarithmicFactorGrowthConstant * positiveLogarithmicSymbol ‖z‖ / (Real.log ‖z‖ / 2) ^ 2 := by
    rw [inv_complexLogReferenceFactor_eq hi, norm_div, div_pow]
    apply div_le_div₀
    · exact mul_nonneg logarithmicFactorGrowthConstant_pos.le
        (zero_le_one.trans (one_le_positiveLogarithmicSymbol _))
    · exact hnum
    · positivity
    · exact hden
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hs

private theorem tendsto_log_factor_left_majorant :
    Tendsto (fun r : ℝ => Real.sqrt
      (logarithmicFactorGrowthConstant * positiveLogarithmicSymbol r / (Real.log r / 2) ^ 2))
      atTop (nhds 0) := by
  have hi := tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hp := (tendsto_positiveLogarithmicSymbol_div_log.mul hi).const_mul
    (4 * logarithmicFactorGrowthConstant)
  simp only [mul_zero] at hp
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hp
  simp only [Real.sqrt_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  dsimp only [Function.comp_def]
  congr 1
  field_simp [(Real.log_pos hr).ne']
  ring

/-- The reciprocal vanishes uniformly at infinity on both sides of the slit. -/
theorem tendsto_inv_complexLogReferenceFactor_nonreal :
    Tendsto (fun z : ℂ => (complexLogReferenceFactor z)⁻¹)
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | z.im ≠ 0}) (nhds 0) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (cocompact ℂ ⊓ 𝓟 {z : ℂ | z.im ≠ 0}) atTop :=
    tendsto_norm_cocompact_atTop.mono_left inf_le_left
  have hb := ((tendsto_log_factor_reciprocal_majorant.max tendsto_log_factor_left_majorant).comp hn)
  simp only [max_self] at hb
  apply squeeze_zero_norm' _ hb
  have hi : ∀ᶠ z in cocompact ℂ ⊓ 𝓟 {z : ℂ | z.im ≠ 0}, z.im ≠ 0 :=
    (Filter.eventually_principal.mpr (fun z hz => hz)).filter_mono inf_le_right
  filter_upwards [hi, hn.eventually_ge_atTop 2] with z hz hR
  by_cases hr : 0 < z.re
  · exact (inv_complexLogReferenceFactor_norm_le hr).trans (le_max_left _ _)
  · exact (inv_complexLogReferenceFactor_norm_le_left (le_of_not_gt hr) hz hR).trans (le_max_right _ _)

#print axioms tendsto_inv_complexLogReferenceFactor_nonreal

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
