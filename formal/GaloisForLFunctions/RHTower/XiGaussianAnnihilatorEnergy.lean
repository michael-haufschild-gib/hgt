import GaloisForLFunctions.RHTower.XiGaussianAnnihilator

/-!
# Fixed positive time: normalized annihilators have vanishing sampled energy

Reciprocal-square summability supplies a fixed head whose complement has
arbitrarily small mass. At a prescribed positive heat time, its product
growth consumes only half the Gaussian decay. The full remaining head
polynomial supplies a summable majorant independent of the growing degree.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section

namespace RHTower

/-- A single head controls all subsequent complete products at one fixed time. -/
theorem exists_xiGaussianAnnihilator_dominating_head (t : {t : ℝ // 0 < t}) :
    ∃ H : Finset XiZeroCopy, ∀ F : Finset XiZeroCopy, ∀ q : XiZeroCopy,
      ‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator (F ∪ H)) t q‖ ≤
        ‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator H) ((t : ℝ) / 2) q‖ := by
  classical
  obtain ⟨H, hH⟩ := xiSpectralPoint_inv_sq_summable.vanishing
    (Iio_mem_nhds (div_pos t.property (show (0 : ℝ) < 16 by positivity)))
  refine ⟨H, fun F q => ?_⟩
  have htail : (∑ p ∈ F \ H, 1 / ‖xiSpectralPoint p‖ ^ 2) < (t : ℝ) / 16 :=
    hH (F \ H) Finset.sdiff_disjoint
  let w := xiSpectralPoint q ^ 2
  have hw : 0 < w.re := xiSpectralSq_re_pos q
  have hsector : ‖w‖ < 2 * w.re := by
    simpa only [w, norm_pow, Complex.sq_norm] using
      xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hnorm : ‖evalRealPolynomial (xiGaussianAnnihilator (F \ H)) w‖ ≤
      Real.exp (2 * ‖w‖ * ((t : ℝ) / 16)) := by
    apply (norm_eval_xiGaussianAnnihilator_le (F \ H) w).trans
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left htail.le (by positivity))
  have hsq : ‖evalRealPolynomial (xiGaussianAnnihilator (F \ H)) w‖ ^ 2 ≤
      Real.exp (((t : ℝ) / 2) * w.re) := by
    calc
      _ ≤ (Real.exp (2 * ‖w‖ * ((t : ℝ) / 16))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = Real.exp (4 * ‖w‖ * ((t : ℝ) / 16)) := by
        rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hsector.le t.property.le]
  rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm,
    xiGaussianAnnihilator_union, evalRealPolynomial_mul, norm_mul, mul_pow]
  change (‖evalRealPolynomial (xiGaussianAnnihilator H) w‖ ^ 2 *
      ‖evalRealPolynomial (xiGaussianAnnihilator (F \ H)) w‖ ^ 2) *
      Real.exp (-((t : ℝ) * w.re)) ≤
    ‖evalRealPolynomial (xiGaussianAnnihilator H) w‖ ^ 2 *
      Real.exp (-(((t : ℝ) / 2) * w.re))
  calc
    _ ≤ (‖evalRealPolynomial (xiGaussianAnnihilator H) w‖ ^ 2 *
        Real.exp (((t : ℝ) / 2) * w.re)) * Real.exp (-((t : ℝ) * w.re)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- The full multiplicity-counted norm energy tends to zero with heat time fixed. -/
theorem tendsto_xiGaussianAnnihilator_energy_zero (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator F) t q‖)
      atTop (𝓝 0) := by
  classical
  obtain ⟨H, hH⟩ := exists_xiGaussianAnnihilator_dominating_head t
  have hpoint (q : XiZeroCopy) : Tendsto
      (fun F : Finset XiZeroCopy =>
        ‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator F) t q‖)
      atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({q} : Finset XiZeroCopy)] with F hF
    have hq : q ∈ F := hF (Finset.mem_singleton_self q)
    simp only [xiPolynomialGaussianHeatTerm,
      xiGaussianAnnihilator_vanishes F ⟨q, hq⟩, zero_pow two_ne_zero, zero_mul, norm_zero]
  have hb : ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ q : XiZeroCopy,
      ‖‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator F) t q‖‖ ≤
        ‖xiPolynomialGaussianHeatTerm (xiGaussianAnnihilator H) ((t : ℝ) / 2) q‖ := by
    filter_upwards [eventually_ge_atTop H] with F hF q
    simpa only [norm_norm, Finset.union_eq_left.mpr hF] using hH F q
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
    (summable_norm_xiPolynomialGaussianHeatTerm (div_pos t.property (by positivity))
      (xiGaussianAnnihilator H)) hpoint hb

/-- An arbitrarily small actual energy is compatible with constant coefficient one. -/
theorem exists_xiGaussian_energy_lt_with_constant_one
    (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∃ P : Polynomial ℝ, P.coeff 0 = 1 ∧
      (∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm P t q‖) < (ε : ℝ) := by
  obtain ⟨F, hF⟩ := ((tendsto_xiGaussianAnnihilator_energy_zero t).eventually
    (Iio_mem_nhds ε.property)).exists
  exact ⟨xiGaussianAnnihilator F, xiGaussianAnnihilator_coeff_zero F, hF⟩

/-- No positive degree-independent floor can control even the constant coefficient. -/
theorem not_exists_xiGaussian_uniform_constant_coefficient_floor
    (t : {t : ℝ // 0 < t}) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ P : Polynomial ℝ,
      c * (P.coeff 0) ^ 2 ≤
        ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm P t q‖ := by
  rintro ⟨c, hc, hfloor⟩
  obtain ⟨P, hP, hsmall⟩ := exists_xiGaussian_energy_lt_with_constant_one t ⟨c, hc⟩
  have h := hfloor P
  rw [hP, one_pow, mul_one] at h
  exact (not_lt_of_ge h) hsmall

end RHTower
