import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorEnergy
import GaloisForLFunctions.RHTower.PolynomialGaussianGammaRadialEnvelope

/-!
# A continuous mass survives the fixed-time annihilators

All finite annihilators stay uniformly positive on one fixed interval around
zero. Their continuous Gaussian mass therefore has a positive floor, even
though their actual divisor energy tends to zero at every fixed positive time.
-/

open Complex Polynomial Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section

namespace RHTower

private theorem one_sub_sum_norm_le_prod {ι : Type*} (F : Finset ι) (u : ι → ℂ)
    (h : ∑ i ∈ F, ‖u i‖ ≤ 1) :
    1 - (∑ i ∈ F, ‖u i‖) ≤ ∏ i ∈ F, ‖1 - u i‖ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi] at h ⊢
    rw [Finset.prod_insert hi]
    have hsum : 0 ≤ ∑ j ∈ F, ‖u j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have htail : ∑ j ∈ F, ‖u j‖ ≤ 1 := by linarith [norm_nonneg (u i)]
    have hfactor : 1 - ‖u i‖ ≤ ‖1 - u i‖ := by
      simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) (u i)
    calc
      _ ≤ (1 - ‖u i‖) * (1 - ∑ j ∈ F, ‖u j‖) := by
        nlinarith [mul_nonneg (norm_nonneg (u i)) hsum]
      _ ≤ ‖1 - u i‖ * ∏ j ∈ F, ‖1 - u j‖ :=
        mul_le_mul hfactor (ih htail) (sub_nonneg.mpr htail) (norm_nonneg _)

/-- The conjugate factors are exactly squared moduli on the real axis. -/
theorem xiGaussianAnnihilator_eval_real (F : Finset XiZeroCopy) (y : ℝ) :
    (xiGaussianAnnihilator F).eval y =
      (∏ q ∈ F, ‖1 - (xiSpectralPoint q ^ 2)⁻¹ * (y : ℂ)‖) ^ 2 := by
  have hfactor (q : XiZeroCopy) :
      evalRealPolynomial (realNormalizedConjFactor ((xiSpectralPoint q ^ 2)⁻¹))
        (y : ℂ) = ((‖1 - (xiSpectralPoint q ^ 2)⁻¹ * (y : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [eval_realNormalizedConjFactor]
    have hc : 1 - (starRingEnd ℂ) ((xiSpectralPoint q ^ 2)⁻¹) * (y : ℂ) =
        (starRingEnd ℂ) (1 - (xiSpectralPoint q ^ 2)⁻¹ * (y : ℂ)) := by simp
    rw [hc, Complex.mul_conj', Complex.ofReal_pow]
  have h := eval_xiGaussianAnnihilator F (y : ℂ)
  rw [evalRealPolynomial_ofReal] at h
  simp only [hfactor, ← Complex.ofReal_prod] at h
  simpa only [Finset.prod_pow] using Complex.ofReal_injective h

/-- One interval works simultaneously for every finite divisor product. -/
theorem exists_xiGaussianAnnihilator_uniform_interval :
    ∃ δ : ℝ, 0 < δ ∧ ∀ F : Finset XiZeroCopy,
      ∀ x : Set.Icc (-δ) δ, (1 / 4 : ℝ) ≤ (xiGaussianAnnihilator F).eval ((x : ℝ) ^ 2) := by
  let S := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  let δ := 1 / (2 * (1 + S))
  have hden : 0 < 2 * (1 + S) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδone : δ ≤ 1 := by
    dsimp only [δ]
    rw [div_le_iff₀ hden]
    linarith
  have hδS : δ * S ≤ 1 / 2 := by
    dsimp only [δ]
    rw [one_div_mul_eq_div, div_le_iff₀ hden]
    linarith
  refine ⟨δ, hδ, fun F x => ?_⟩
  have hx : |(x : ℝ)| ≤ δ := abs_le.mpr x.property
  have habs : (x : ℝ) ^ 2 ≤ δ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hδ.le).mpr hx
  have hxsq : (x : ℝ) ^ 2 ≤ δ := by nlinarith
  have hfin : (∑ q ∈ F, 1 / ‖xiSpectralPoint q‖ ^ 2) ≤ S :=
    xiSpectralPoint_inv_sq_summable.sum_le_tsum F (fun _ _ => by positivity)
  have hu : (∑ q ∈ F,
      ‖(xiSpectralPoint q ^ 2)⁻¹ * (((x : ℝ) ^ 2 : ℝ) : ℂ)‖) ≤ 1 / 2 := by
    simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, ← Finset.sum_mul]
    simp only [← one_div]
    change (∑ q ∈ F, 1 / ‖xiSpectralPoint q‖ ^ 2) * (x : ℝ) ^ 2 ≤ _
    calc
      _ ≤ S * (x : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hfin (sq_nonneg _)
      _ ≤ S * δ := mul_le_mul_of_nonneg_left hxsq hS
      _ ≤ 1 / 2 := by simpa only [mul_comm] using hδS
  have hprod := one_sub_sum_norm_le_prod F
    (fun q => (xiSpectralPoint q ^ 2)⁻¹ * (((x : ℝ) ^ 2 : ℝ) : ℂ))
    (show (∑ q ∈ F, ‖(xiSpectralPoint q ^ 2)⁻¹ * (((x : ℝ) ^ 2 : ℝ) : ℂ)‖) ≤ 1 by
      linarith)
  rw [xiGaussianAnnihilator_eval_real]
  nlinarith

/-- Continuous Gaussian mass stays bounded below independently of degree. -/
theorem exists_xiGaussianAnnihilator_uniform_mass_lower (t : {t : ℝ // 0 < t}) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : Finset XiZeroCopy,
      c ≤ routeUPolynomialGaussianMass (xiGaussianAnnihilator F) t := by
  obtain ⟨δ, hδ, hinterval⟩ := exists_xiGaussianAnnihilator_uniform_interval
  let b := Real.exp (-((t : ℝ) * δ ^ 2)) / 16
  have hb : 0 < b := by dsimp only [b]; positivity
  refine ⟨(2 * δ) * b, mul_pos (by linarith) hb, fun F => ?_⟩
  have hint := integrable_norm_routeUPolynomialGaussianDensity (xiGaussianAnnihilator F) t
  have hpoint : ∀ x ∈ Set.Icc (-δ) δ,
      b ≤ ‖routeUPolynomialGaussianDensity (xiGaussianAnnihilator F) t x‖ := by
    intro x hx
    have hp := hinterval F ⟨x, hx⟩
    have hxsq : x ^ 2 ≤ δ ^ 2 := by
      nlinarith [sq_nonneg (x - δ), sq_nonneg (x + δ),
        mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1)]
    have he : Real.exp (-((t : ℝ) * δ ^ 2)) ≤ Real.exp (-((t : ℝ) * x ^ 2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hxsq t.property.le))
    rw [routeUPolynomialGaussianDensity, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), GaloisForLFunctions.evenSquarePolynomial,
      Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
    dsimp only [b]
    have hp2 : (1 / 16 : ℝ) ≤ ((xiGaussianAnnihilator F).eval (x ^ 2)) ^ 2 := by nlinarith
    have hh := mul_le_mul hp2 he (Real.exp_pos _).le (sq_nonneg _)
    nlinarith
  have hconst : IntegrableOn (fun _ : ℝ => b) (Set.Icc (-δ) δ) volume :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  calc
    _ = ∫ _ in Set.Icc (-δ) δ, b := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      ring
    _ ≤ ∫ x in Set.Icc (-δ) δ,
        ‖routeUPolynomialGaussianDensity (xiGaussianAnnihilator F) t x‖ :=
      setIntegral_mono_on hconst hint.integrableOn measurableSet_Icc hpoint
    _ ≤ routeUPolynomialGaussianMass (xiGaussianAnnihilator F) t :=
      setIntegral_le_integral hint (Eventually.of_forall fun _ => norm_nonneg _)

/-- A fixed-time degree-independent continuous-mass floor is impossible. -/
theorem not_exists_xiGaussian_uniform_mass_floor (t : {t : ℝ // 0 < t}) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℝ,
      c * routeUPolynomialGaussianMass P t ≤
        ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm P t q‖ := by
  rintro ⟨c, hc, hfloor⟩
  obtain ⟨m, hm, hmass⟩ := exists_xiGaussianAnnihilator_uniform_mass_lower t
  obtain ⟨F, hF⟩ := ((tendsto_xiGaussianAnnihilator_energy_zero t).eventually
    (Iio_mem_nhds (mul_pos hc hm))).exists
  exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left (hmass F) hc.le).trans
    (hfloor (xiGaussianAnnihilator F)))) hF

end RHTower
