import GaloisForLFunctions.RHTower.XiGaussianUniformHeatHalfLine
import GaloisForLFunctions.RHTower.XiGaussianUniformTailObstruction

/-!
# Fixed polar value with vanishing native Xi energy

Every finite normalized divisor product is at least one on the nonpositive
real axis. Normalizing at the polar evaluation point therefore preserves
vanishing native energy while fixing the polar value exactly at one.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

theorem xiGaussianNativeEnergy_C_mul (c : ℝ) (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianNativeEnergy (Polynomial.C c * P) t = c ^ 2 * xiGaussianNativeEnergy P t := by
  unfold xiGaussianNativeEnergy
  have heval (z : ℂ) : evalRealPolynomial (Polynomial.C c) z = (c : ℂ) := by
    simp [evalRealPolynomial]
  simp_rw [norm_xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul, heval,
    norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_assoc]
  rw [tsum_mul_left]

theorem one_le_realNormalizedConjFactor_eval_nonpos (q : XiZeroCopy)
    (x : Set.Iic (0 : ℝ)) :
    1 ≤ (realNormalizedConjFactor ((xiSpectralPoint q ^ 2)⁻¹)).eval (x : ℝ) := by
  let a := (xiSpectralPoint q ^ 2)⁻¹
  have ha : 0 ≤ a.re := by
    rw [Complex.inv_re]
    exact div_nonneg (xiSpectralSq_re_pos q).le (Complex.normSq_nonneg _)
  have hax := mul_nonpos_of_nonneg_of_nonpos ha x.property
  have hs := mul_nonneg (Complex.normSq_nonneg a) (sq_nonneg (x : ℝ))
  simp only [realNormalizedConjFactor, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X]
  change 1 ≤ 1 - 2 * a.re * (x : ℝ) + Complex.normSq a * (x : ℝ) ^ 2
  nlinarith only [hax, hs]

theorem one_le_xiGaussianAnnihilator_eval_nonpos (F : Finset XiZeroCopy)
    (x : Set.Iic (0 : ℝ)) :
    1 ≤ (xiGaussianAnnihilator F).eval (x : ℝ) := by
  rw [xiGaussianAnnihilator, Polynomial.eval_prod]
  exact Finset.one_le_prod fun q _ => one_le_realNormalizedConjFactor_eval_nonpos q x

/-- Polar normalization retains every finite divisor factor. -/
def xiGaussianPolarAnnihilator (F : Finset XiZeroCopy) : Polynomial ℝ :=
  Polynomial.C ((xiGaussianAnnihilator F).eval (-(1 / 4 : ℝ)))⁻¹ * xiGaussianAnnihilator F

theorem xiGaussianPolarAnnihilator_eval_pole (F : Finset XiZeroCopy) :
    (xiGaussianPolarAnnihilator F).eval (-(1 / 4 : ℝ)) = 1 := by
  have ha : 0 < (xiGaussianAnnihilator F).eval (-(1 / 4 : ℝ)) :=
    zero_lt_one.trans_le (one_le_xiGaussianAnnihilator_eval_nonpos F
      ⟨_, neg_nonpos.mpr (by positivity : 0 ≤ (1 / 4 : ℝ))⟩)
  rw [xiGaussianPolarAnnihilator, Polynomial.eval_mul, Polynomial.eval_C, inv_mul_cancel₀ ha.ne']

theorem xiGaussianPolarAnnihilator_energy_le (F : Finset XiZeroCopy)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t ≤
      xiGaussianNativeEnergy (xiGaussianAnnihilator F) t := by
  let a := (xiGaussianAnnihilator F).eval (-(1 / 4 : ℝ))
  have ha : 1 ≤ a := one_le_xiGaussianAnnihilator_eval_nonpos F
    ⟨_, neg_nonpos.mpr (by positivity : 0 ≤ (1 / 4 : ℝ))⟩
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hi : a⁻¹ ≤ 1 := (inv_le_one₀ ha0).mpr ha
  have hs : a⁻¹ ^ 2 ≤ 1 := by nlinarith [inv_nonneg.mpr ha0.le]
  rw [xiGaussianPolarAnnihilator, xiGaussianNativeEnergy_C_mul]
  exact (mul_le_mul_of_nonneg_right hs (xiGaussianNativeEnergy_nonneg _ t)).trans_eq (one_mul _)

theorem xiGaussianPolarAnnihilator_energy_pos (F : Finset XiZeroCopy)
    (t : {t : ℝ // 0 < t}) :
    0 < xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t := by
  have ha : 0 < (xiGaussianAnnihilator F).eval (-(1 / 4 : ℝ)) :=
    zero_lt_one.trans_le (one_le_xiGaussianAnnihilator_eval_nonpos F
      ⟨_, neg_nonpos.mpr (by positivity : 0 ≤ (1 / 4 : ℝ))⟩)
  rw [xiGaussianPolarAnnihilator, xiGaussianNativeEnergy_C_mul]
  exact mul_pos (sq_pos_of_pos (inv_pos.mpr ha)) (xiGaussianNativeEnergy_annihilator_pos F t)

/-- The fixed nonzero polar value survives while full native energy tends to zero. -/
theorem tendsto_xiGaussianPolarAnnihilator_energy_zero (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy => xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ => xiGaussianNativeEnergy_nonneg _ t)
    (fun F => xiGaussianPolarAnnihilator_energy_le F t)
    (tendsto_xiGaussianNativeEnergy_annihilator_zero t)

end RHTower
