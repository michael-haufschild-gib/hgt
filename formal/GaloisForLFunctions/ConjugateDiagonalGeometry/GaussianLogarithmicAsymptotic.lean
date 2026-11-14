import GaloisForLFunctions.ConjugateDiagonalGeometry.LogarithmicBoundaryNormalization
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.HTGeometry.PolynomialExponentialDomination
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# The logarithmic main term of the translated Gaussian zero sum

The quarter-line digamma density differs from the logarithm of height by a
bounded quantity. Gaussian convolution preserves its leading coefficient;
the absolutely convergent prime series contributes only a bounded remainder.
-/

open Filter Topology MeasureTheory Complex Set

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open RiemannGaussian

/-- The real archimedean density has bounded error on the logarithmic scale,
uniformly at positive and negative heights. -/
theorem abs_riemannArchimedeanDensity_sub_log_le {t : ℝ} (ht : 4 ≤ |t|) :
    |riemannArchimedeanDensity t - Real.log |t|| ≤ 3 := by
  let z : ℂ := 1 / 4 + I * (t / 2)
  have ht0 : 0 < |t| := by linarith only [ht]
  have hzre : 0 < z.re := by norm_num [z]
  have him : |t| / 2 ≤ ‖z‖ := by
    simpa [z, abs_div] using Complex.abs_im_le_norm z
  have hz2 : 2 ≤ ‖z‖ := by linarith only [him, ht]
  have hz0 : 0 < ‖z‖ := by linarith only [hz2]
  have hnorm : ‖z‖ ≤ |t| := by
    calc ‖z‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖I * (t / 2 : ℂ)‖ := norm_add_le _ _
      _ = 1 / 4 + |t| / 2 := by norm_num [norm_mul, norm_div]
      _ ≤ |t| := by linarith only [ht]
  have hloglo := Real.log_le_log (by positivity : 0 < |t| / 2) him
  rw [Real.log_div ht0.ne' (by norm_num)] at hloglo
  have hloghi := Real.log_le_log hz0 hnorm
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hgap : |Real.log ‖z‖ - Real.log |t|| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hloglo, hlog2], by linarith only [hloghi]⟩
  have hrem := (Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)).trans
    (HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hz2)
  rw [Complex.sub_re, Complex.log_re] at hrem
  have hquot : 3 / ‖z‖ ≤ 3 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz2
  calc |riemannArchimedeanDensity t - Real.log |t||
      = |((Complex.digamma z).re - Real.log ‖z‖) +
          (Real.log ‖z‖ - Real.log |t|)| := by
            congr 1
            change (Complex.digamma z).re - _ = _
            ring
    _ ≤ |(Complex.digamma z).re - Real.log ‖z‖| +
          |Real.log ‖z‖ - Real.log |t|| := abs_add_le _ _
    _ ≤ 3 := by linarith only [hrem, hquot, hgap]

/-- The archimedean density has logarithmic coefficient one at both ends. -/
theorem tendsto_riemannArchimedeanDensity_log_normalized :
    Tendsto (fun t => (riemannArchimedeanDensity t : ℂ) / (Real.log |t| : ℂ))
      (Filter.comap abs atTop) (𝓝 1) := by
  apply tendsto_log_normalized_of_epsilon_bound
  intro ε hε
  refine ⟨max 8 (Real.exp (3 / ε)), le_max_left _ _, ?_⟩
  intro t ht
  have ht8 : 8 ≤ |t| := (le_max_left _ _).trans ht
  have hlog : 3 / ε ≤ Real.log |t| := by
    have hh := Real.log_le_log (Real.exp_pos (3 / ε))
      ((le_max_right _ _).trans ht)
    simpa only [Real.log_exp] using hh
  have hh := mul_le_mul_of_nonneg_left hlog hε.le
  rw [mul_div_cancel₀ _ hε.ne'] at hh
  simpa only [mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    (abs_riemannArchimedeanDensity_sub_log_le (by linarith only [ht8])).trans hh

/-- The archimedean density admits a global logarithmic majorant, including
the compact interval around the origin. -/
theorem exists_riemannArchimedeanDensity_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖(riemannArchimedeanDensity t : ℂ)‖ ≤ C * Real.log (2 + |t|) := by
  apply exists_global_logarithmic_bound_of_eventual
    (Complex.continuous_ofReal.comp continuous_riemannArchimedeanDensity)
    (K := 4) (by norm_num)
  refine ⟨8, le_rfl, ?_⟩
  intro t ht
  have hl : 1 ≤ Real.log |t| := by
    have he : Real.exp 1 ≤ |t| := by
      have he := Real.exp_one_lt_d9
      linarith only [he, ht]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hb := abs_riemannArchimedeanDensity_sub_log_le
    (by linarith only [ht] : 4 ≤ |t|)
  have ha : |riemannArchimedeanDensity t| ≤ 3 + Real.log |t| := by
    calc |riemannArchimedeanDensity t|
        = |(riemannArchimedeanDensity t - Real.log |t|) + Real.log |t|| := by ring_nf
      _ ≤ |riemannArchimedeanDensity t - Real.log |t|| + |Real.log |t|| := abs_add_le _ _
      _ ≤ 3 + Real.log |t| := by
        rw [abs_of_nonneg (by linarith only [hl] : 0 ≤ Real.log |t|)]
        exact add_le_add_right hb _
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith only [ha, hl]

private theorem integrable_gaussian_log_weight {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ => Real.exp (-ε * u ^ 2) *
      (2 + |u| / Real.log 2)) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let M : ℝ := 2 + (1 + 2 / ε) / Real.log 2
  have hg := (integrable_exp_neg_mul_sq (by positivity : 0 < ε / 2)).const_mul M
  apply hg.mono' (by fun_prop)
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp := HTGeometry.pow_mul_exp_neg_le (by positivity : 0 < ε / 2) 1 (sq_nonneg u)
  norm_num only [pow_one, Nat.factorial_one, Nat.cast_one] at hp
  have hp' : u ^ 2 * Real.exp (-(ε / 2 * u ^ 2)) ≤ 2 / ε := by
    convert hp using 1 <;> field_simp [hε.ne'] <;> ring
  have he : Real.exp (-(ε / 2 * u ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by positivity)
  have hu : |u| ≤ 1 + u ^ 2 := by
    nlinarith only [sq_nonneg (|u| - 1), sq_abs u]
  have hweighted : (2 + |u| / Real.log 2) * Real.exp (-(ε / 2 * u ^ 2)) ≤ M := by
    have hh := mul_le_mul_of_nonneg_right hu (Real.exp_nonneg (-(ε / 2 * u ^ 2)))
    have hdiv := div_le_div_of_nonneg_right hh hl.le
    dsimp [M]
    have hsum : (Real.exp (-(ε / 2 * u ^ 2)) +
        u ^ 2 * Real.exp (-(ε / 2 * u ^ 2))) / Real.log 2 ≤ (1 + 2 / ε) / Real.log 2 :=
      div_le_div_of_nonneg_right (add_le_add he hp') hl.le
    nlinarith only [hdiv, hsum, he]
  calc Real.exp (-ε * u ^ 2) * (2 + |u| / Real.log 2)
      = Real.exp (-(ε / 2 * u ^ 2)) *
          ((2 + |u| / Real.log 2) * Real.exp (-(ε / 2 * u ^ 2))) := by
            have heq : Real.exp (-ε * u ^ 2) =
                Real.exp (-(ε / 2 * u ^ 2)) * Real.exp (-(ε / 2 * u ^ 2)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [heq]
            ring
    _ ≤ Real.exp (-(ε / 2 * u ^ 2)) * M :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_nonneg _)
    _ = M * Real.exp (-(ε / 2) * u ^ 2) := by rw [neg_mul]; ring

/-- The real density is even by conjugation of the digamma function. -/
theorem riemannArchimedeanDensity_neg (t : ℝ) :
    riemannArchimedeanDensity (-t) = riemannArchimedeanDensity t := by
  have hz : starRingEnd ℂ (1 / 4 + I * (t / 2 : ℂ)) =
      1 / 4 + I * ((-t) / 2 : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  unfold riemannArchimedeanDensity
  rw [← hz, ReflectedDigammaAnomaly.digamma_conj]
  rfl

/-- The positive-half-line symmetric integral is one full translated integral. -/
theorem gaussianDigammaIntegral_eq_full {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    gaussianDigammaIntegral ε T = (1 / Real.pi) *
      ∫ u : ℝ, Real.exp (-ε * u ^ 2) * riemannArchimedeanDensity (T + u) := by
  let f : ℝ → ℝ := fun r => translatedGaussian ε T r * riemannArchimedeanDensity r
  have hf : Integrable f := integrable_translatedGaussian_mul_riemannArchimedeanDensity hε T
  have heq : (fun r => symmetricGaussian ε T r * riemannArchimedeanDensity r) =
      fun r => f r + f (-r) := by
    funext r
    simp only [f, symmetricGaussian, riemannArchimedeanDensity_neg, add_mul]
  unfold gaussianDigammaIntegral
  rw [heq, integral_add hf.integrableOn (hf.comp_neg.integrableOn),
    integral_comp_neg_Ioi, neg_zero, add_comm]
  rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hf.integrableOn hf.integrableOn, Iic_union_Ioi, setIntegral_univ]
  congr 1
  rw [← integral_add_left_eq_self f T]
  apply integral_congr_ae
  filter_upwards with u
  simp only [f, translatedGaussian, add_sub_cancel_left]

/-- Gaussian averaging multiplies the logarithmic density coefficient by its mass. -/
theorem tendsto_gaussianDigammaIntegral_log_normalized {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T => gaussianDigammaIntegral ε T / Real.log |T|)
      (Filter.comap abs atTop) (𝓝 (Real.sqrt (Real.pi / ε) / Real.pi)) := by
  obtain ⟨C, hC, hb⟩ := exists_riemannArchimedeanDensity_log_bound
  let k : ℝ → ℂ := fun u => (Real.exp (-ε * u ^ 2) : ℂ)
  have hw : Integrable (fun u => ‖k u‖ * (2 + |u| / Real.log 2)) := by
    simpa only [k, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      integrable_gaussian_log_weight hε
  have hc := tendsto_integral_mul_log_normalized
    (T := fun T : ℝ => T) Filter.tendsto_comap
    (Complex.continuous_ofReal.comp continuous_riemannArchimedeanDensity)
    tendsto_riemannArchimedeanDensity_log_normalized hC hb
    (k := k) (by fun_prop) hw
  have hm : (∫ u, k u) = (Real.sqrt (Real.pi / ε) : ℂ) := by
    dsimp [k]
    rw [integral_complex_ofReal, integral_gaussian]
  rw [hm, mul_one] at hc
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  simp only [Function.comp_def, k, ← Complex.ofReal_mul, integral_complex_ofReal,
    Complex.div_ofReal_re, Complex.ofReal_re] at hr
  have hh := hr.const_mul (1 / Real.pi)
  convert hh using 1
  · funext T
    rw [gaussianDigammaIntegral_eq_full hε T]
    ring
  · congr 1
    ring

private theorem tendsto_bounded_div_log {f : ℝ → ℝ} {B : ℝ}
    (hb : ∀ T, |f T| ≤ B) :
    Tendsto (fun T => f T / Real.log |T|) (Filter.comap abs atTop) (𝓝 0) := by
  have hl := Real.tendsto_log_atTop.comp (Filter.tendsto_comap (f := abs))
  apply squeeze_zero_norm' ?_ (hl.const_div_atTop B)
  filter_upwards [Filter.tendsto_comap.eventually (eventually_ge_atTop (2 : ℝ))] with T hT
  have hlog : 0 < Real.log |T| := Real.log_pos (by linarith only [hT])
  simpa only [Real.norm_eq_abs, abs_div, abs_of_pos hlog] using
    div_le_div_of_nonneg_right (hb T) hlog.le

/-- The prime series has a uniform bound in its center. -/
theorem abs_gaussianPrimeContribution_le {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    |gaussianPrimeContribution ε T| ≤ gaussianPrimeContribution ε 0 := by
  have h0 := summable_gaussianPrimeSummand hε 0
  have hT := summable_gaussianPrimeSummand hε T
  have hb (n : ℕ) : |gaussianPrimeSummand ε T n| ≤ gaussianPrimeSummand ε 0 n := by
    simp only [gaussianPrimeSummand, zero_mul, Real.cos_zero, mul_one, abs_mul]
    have ha : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := by positivity
    rw [abs_of_nonneg ha, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have hsum : |gaussianPrimeSum ε T| ≤ gaussianPrimeSum ε 0 := by
    apply abs_le.mpr
    constructor
    · have hh := Summable.tsum_le_tsum (fun n => (abs_le.mp (hb n)).1) h0.neg hT
      simpa only [gaussianPrimeSum, tsum_neg] using hh
    · exact Summable.tsum_le_tsum (fun n => (abs_le.mp (hb n)).2) hT h0
  unfold gaussianPrimeContribution
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / Real.sqrt (Real.pi * ε))]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

private theorem bounded_gaussianArchimedeanRemainder {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    |gaussianArchimedeanContribution ε T - gaussianDigammaIntegral ε T| ≤
      4 * Real.exp (ε / 4) + |Real.log Real.pi / Real.sqrt (Real.pi * ε)| := by
  have he : Real.exp (ε / 4 - ε * T ^ 2) ≤ Real.exp (ε / 4) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hε.le (sq_nonneg T)]
  have hp : |4 * Real.exp (ε / 4 - ε * T ^ 2) * Real.cos (ε * T)| ≤
      4 * Real.exp (ε / 4) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)).trans
      (mul_le_mul_of_nonneg_left he (by norm_num))
  unfold gaussianArchimedeanContribution
  rw [add_sub_cancel_right]
  exact (abs_sub _ _).trans (add_le_add_right hp _)

/-- The actual translated Gaussian zero sum has the logarithmic coefficient
predicted by the archimedean mass. -/
theorem tendsto_canonicalZetaGaussianZeroSum_log_normalized {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun T => canonicalZetaGaussianZeroSum ε T / Real.log |T|)
      (Filter.comap abs atTop) (𝓝 (Real.sqrt (Real.pi / ε) / (2 * Real.pi))) := by
  have hd := tendsto_gaussianDigammaIntegral_log_normalized hε
  have hr := tendsto_bounded_div_log (bounded_gaussianArchimedeanRemainder hε)
  have hp := tendsto_bounded_div_log (abs_gaussianPrimeContribution_le hε)
  have hh := ((hd.add hr).sub hp).div_const 2
  simp only [add_zero, sub_zero] at hh
  convert hh using 1
  · funext T
    have he := gaussianArithmeticExplicitFormula_eq_canonical hε T
    unfold gaussianArithmeticExplicitFormula canonicalZetaSymmetricGaussianZeroSum at he
    rw [show canonicalZetaGaussianZeroSum ε T =
      (gaussianDigammaIntegral ε T +
        (gaussianArchimedeanContribution ε T - gaussianDigammaIntegral ε T) -
        gaussianPrimeContribution ε T) / 2 by linarith only [he]]
    ring
  · congr 1
    ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_riemannArchimedeanDensity_log_normalized

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_canonicalZetaGaussianZeroSum_log_normalized
