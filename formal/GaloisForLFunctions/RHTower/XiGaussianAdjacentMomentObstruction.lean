import GaloisForLFunctions.RHTower.XiGaussianTransverseMomentBudget
import GaloisForLFunctions.RHTower.XiGaussianNativeHeatCutoff

/-!
# Native adjacent moments cannot be absorbed uniformly over polynomial order

One complete low-shell annihilator makes both the first native moment and
the next native energy arbitrarily large relative to native mass. The same
polynomial works at every positive heat time and in any prescribed nonzero
principal ideal. Thus the small transverse correction coefficient does not
justify replacing its higher moment by a constant times native mass.
This does not assert an off-critical zero or a negative Xi witness.
-/

open Complex Polynomial
noncomputable section
namespace RHTower

private theorem shell_atom_zero (B : Polynomial ℝ) (R t : ℝ)
    (q : XiZeroCopy) (hq : (xiSpectralPoint q ^ 2).re ≤ R) :
    xiPolynomialGaussianHeatTerm
      (B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset) t q = 0 := by
  have hm : q ∈ (finite_xiHeatShell R).toFinset := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
  simp only [xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul,
    xiGaussianAnnihilator_vanishes _ ⟨q, hm⟩, mul_zero, zero_pow two_ne_zero, zero_mul]

/-- The complete surviving native mass lies above the chosen first-moment level. -/
theorem xiGaussianNativeFirstMoment_shell_floor (B : Polynomial ℝ) (R : ℝ)
    (t : {t : ℝ // 0 < t}) :
    let P := B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset
    R * xiGaussianNativeEnergy P t ≤ xiGaussianNativeFirstMoment P t := by
  let P := B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset
  have hp (q : XiZeroCopy) : R * ‖xiPolynomialGaussianHeatTerm P t q‖ ≤
      (xiSpectralPoint q ^ 2).re * ‖xiPolynomialGaussianHeatTerm P t q‖ := by
    by_cases hq : (xiSpectralPoint q ^ 2).re ≤ R
    · have hz : xiPolynomialGaussianHeatTerm P t q = 0 := shell_atom_zero B R t q hq
      simp only [hz, norm_zero, mul_zero, le_refl]
    · exact mul_le_mul_of_nonneg_right (le_of_not_ge hq) (norm_nonneg _)
  have h := Summable.tsum_le_tsum hp
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property P).mul_left R)
    (summable_xiGaussianNativeFirstMoment P t)
  rw [tsum_mul_left] at h
  exact h

/-- The same shell forces a squared cutoff in the next native energy. -/
theorem xiGaussianNativeNextEnergy_shell_floor (B : Polynomial ℝ) (R : NNReal)
    (t : {t : ℝ // 0 < t}) :
    let P := B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset
    (R : ℝ) ^ 2 * xiGaussianNativeEnergy P t ≤ xiGaussianNativeEnergy (P * X) t := by
  let P := B * xiGaussianAnnihilator (finite_xiHeatShell R).toFinset
  have hp (q : XiZeroCopy) : (R : ℝ) ^ 2 * ‖xiPolynomialGaussianHeatTerm P t q‖ ≤
      ‖xiPolynomialGaussianHeatTerm (P * X) t q‖ := by
    by_cases hq : (xiSpectralPoint q ^ 2).re ≤ R
    · have hz : xiPolynomialGaussianHeatTerm P t q = 0 := shell_atom_zero B R t q hq
      rw [hz, norm_zero, mul_zero]
      exact norm_nonneg _
    · have hs : (R : ℝ) ^ 2 ≤ ‖xiSpectralPoint q ^ 2‖ ^ 2 :=
        (sq_le_sq₀ R.property (norm_nonneg _)).mpr
          ((le_of_not_ge hq).trans (Complex.re_le_norm _))
      have h := mul_le_mul_of_nonneg_right hs (norm_nonneg (xiPolynomialGaussianHeatTerm P t q))
      rw [norm_xiPolynomialGaussianHeatTerm, norm_xiPolynomialGaussianHeatTerm,
        evalRealPolynomial_mul P X, evalRealPolynomial_X, norm_mul, mul_pow]
      rw [norm_xiPolynomialGaussianHeatTerm] at h
      nlinarith only [h]
  have h := Summable.tsum_le_tsum hp
    ((summable_norm_xiPolynomialGaussianHeatTerm t.property P).mul_left ((R : ℝ) ^ 2))
    (summable_norm_xiPolynomialGaussianHeatTerm t.property (P * X))
  rw [tsum_mul_left] at h
  exact h

/-- One polynomial defeats both proposed moment absorptions at every positive time. -/
theorem exists_xiGaussian_principalIdeal_allTime_large_moments
    (B : {B : Polynomial ℝ // B ≠ 0}) (C : ℝ) :
    ∃ P : Polynomial ℝ, B.1 ∣ P ∧ ∀ t : {t : ℝ // 0 < t},
      0 < xiGaussianNativeEnergy P t ∧
      C * xiGaussianNativeEnergy P t < xiGaussianNativeFirstMoment P t ∧
      C * xiGaussianNativeEnergy P t < xiGaussianNativeEnergy (P * X) t := by
  let R : NNReal := ⟨max 1 (C+1), zero_le_one.trans (le_max_left _ _)⟩
  have hR : 1 ≤ (R : ℝ) := le_max_left _ _
  have hCR : C < (R : ℝ) := by
    have h := le_max_right (1 : ℝ) (C+1)
    change C < max 1 (C+1)
    linarith only [h]
  have hCR₂ : C < (R : ℝ) ^ 2 := by nlinarith only [hCR, hR]
  let F := (finite_xiHeatShell R).toFinset
  let P := B.1 * xiGaussianAnnihilator F
  have hAnn : xiGaussianAnnihilator F ≠ 0 := by
    intro hz
    have h := xiGaussianAnnihilator_zero F
    rw [hz, Polynomial.eval_zero] at h
    exact zero_ne_one h
  have hP : P ≠ 0 := mul_ne_zero B.property hAnn
  refine ⟨P, dvd_mul_right _ _, fun t => ?_⟩
  have hK := xiGaussianNativeEnergy_pos ⟨P, hP⟩ t
  refine ⟨hK, ?_, ?_⟩
  · exact (mul_lt_mul_of_pos_right hCR hK).trans_le
      (xiGaussianNativeFirstMoment_shell_floor B.1 R t)
  · exact (mul_lt_mul_of_pos_right hCR₂ hK).trans_le
      (xiGaussianNativeNextEnergy_shell_floor B.1 R t)

theorem not_xiGaussian_principalIdeal_firstMoment_absorption
    (B : {B : Polynomial ℝ // B ≠ 0}) (t : {t : ℝ // 0 < t}) :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℝ, B.1 ∣ P →
      xiGaussianNativeFirstMoment P t ≤ C * xiGaussianNativeEnergy P t := by
  rintro ⟨C, hC⟩
  obtain ⟨P, hB, h⟩ := exists_xiGaussian_principalIdeal_allTime_large_moments B C
  exact (not_lt_of_ge (hC P hB)) (h t).2.1

theorem not_xiGaussian_principalIdeal_nextEnergy_absorption
    (B : {B : Polynomial ℝ // B ≠ 0}) (t : {t : ℝ // 0 < t}) :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℝ, B.1 ∣ P →
      xiGaussianNativeEnergy (P * X) t ≤ C * xiGaussianNativeEnergy P t := by
  rintro ⟨C, hC⟩
  obtain ⟨P, hB, h⟩ := exists_xiGaussian_principalIdeal_allTime_large_moments B C
  exact (not_lt_of_ge (hC P hB)) (h t).2.2

end RHTower
