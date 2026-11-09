import GaloisForLFunctions.EulerFETransportTheory.GaussianRenormalizationAtZeros
import GaloisForLFunctions.InfiniteRankWeilTheory.TheTowersOfZeta

/-!
# The raw prime current at a rightmost zero

At a rightmost zero, every nonresonant Gamma mode is bounded at small damping.
Their full absolutely summable field therefore disappears after division by
logarithmic scale. The raw prime-minus-continuum current then recovers the
actual divisor multiplicity, without a counterterm in the observable.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Rightmostness bounds the whole nonresonant field, even without a uniform
gap or a finite layer at that abscissa. -/
theorem norm_nonresonantGaussianModes_le_of_rightmost (ρ : XiDivisorSupport)
    (htop : ∀ q : XiZeroCopy, (xiZero q).re ≤ (ρ : ℂ).re)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖nonresonantGaussianModes ρ y‖ ≤
      ∑' q : NonresonantZero ρ, ‖gaussianMBKernel 1 (xiZero q - ρ)‖ := by
  have hmode : ∀ q : NonresonantZero ρ,
      ‖gaussianMBKernel y (xiZero q - ρ)‖ ≤ ‖gaussianMBKernel 1 (xiZero q - ρ)‖ := by
    intro q
    simp only [gaussianMBKernel, Complex.ofReal_one, Complex.one_cpow, mul_one]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have he : 0 ≤ (-((xiZero q - (ρ : ℂ)) / 2)).re := by
      simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.sub_re]
      linarith [htop q]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.rpow_le_one hy.le hy1 he)
  exact (norm_tsum_le_tsum_norm (summable_norm_nonresonantGaussianModes ρ hy)).trans
    ((summable_norm_nonresonantGaussianModes ρ hy).tsum_le_tsum hmode
      (summable_norm_nonresonantGaussianModes ρ zero_lt_one))

/-- The raw Gaussian prime discrepancy reads the divisor multiplicity at a
rightmost zero. No Gamma counterterm appears in this observable. -/
theorem tendsto_gaussianPrimeGap_div_logScale_of_rightmost (ρ : XiDivisorSupport)
    (htop : ∀ q : XiZeroCopy, (xiZero q).re ≤ (ρ : ℂ).re) :
    Tendsto (fun u : ℝ => gaussianPrimeContinuumGap ρ (Real.exp (-u)) / (u : ℂ))
      atTop (𝓝 (-(((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℂ) / 2)) := by
  rw [← card_xiZeroCopyFiber ρ]
  have hscale : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot,
      Eventually.of_forall fun u => Real.exp_pos (-u)⟩
  have hinv : Tendsto (fun u : ℝ => (u : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  let A : ℝ := ∑' q : NonresonantZero ρ, ‖gaussianMBKernel 1 (xiZero q - ρ)‖
  have hB : Tendsto (fun u : ℝ => nonresonantGaussianModes ρ (Real.exp (-u)) / (u : ℂ))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hb : Tendsto (fun u : ℝ => A / u) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul A
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    exact div_le_div_of_nonneg_right
      (norm_nonresonantGaussianModes_le_of_rightmost ρ htop (Real.exp_pos _)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.le))) hu.le
  have h := (((tendsto_gaussianPrimeGap_logarithmicFinitePart ρ).comp hscale).mul hinv).sub hB
  have hfinal := h.sub_const (((xiZeroCopyFiber ρ).card : ℂ) / 2)
  simp only [mul_zero, sub_zero, zero_sub] at hfinal
  rw [← neg_div] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  dsimp only [Function.comp_def]
  rw [Real.log_exp, Complex.ofReal_neg]
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  field_simp
  ring

/-- Failure of AAL produces an actual off-line top zero whose multiplicity is
visible in the raw prime current at logarithmic Gaussian scale. -/
theorem not_asymptoticAbscissaLaw_has_primeMultiplicityLimit
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ ρ : XiDivisorSupport, 1 / 2 < (ρ : ℂ).re ∧
      Tendsto (fun u : ℝ => gaussianPrimeContinuumGap ρ (Real.exp (-u)) / (u : ℂ))
        atTop (𝓝 (-(((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℂ) / 2)) := by
  classical
  rw [InfiniteRankWeilTheory.asymptoticAbscissaLaw_zetaConfig_iff,
    InfiniteRankWeilTheory.not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨F, β, θ, hF, hβ, hθ, htop, hrest⟩ := hnot
  obtain ⟨q, hq⟩ := hF
  have hqβ : (q.1 : ℂ).re = β := htop q hq
  refine ⟨q.1, by rw [hqβ]; exact hβ, ?_⟩
  apply tendsto_gaussianPrimeGap_div_logScale_of_rightmost
  intro p
  rw [hqβ]
  by_cases hp : p ∈ F
  · exact (htop p hp).le
  · exact (hrest p hp).trans hθ.le

#print axioms tendsto_gaussianPrimeGap_div_logScale_of_rightmost
#print axioms not_asymptoticAbscissaLaw_has_primeMultiplicityLimit

end GaloisForLFunctions.EulerFETransportTheory
