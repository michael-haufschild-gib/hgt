import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPoissonMode
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Every logarithmic order of the homogeneous Poisson integral

Two neighboring strip exponents dominate every logarithmic moment. Thus arbitrary
polynomial boundary weights define actual convergent integrals, without a bound
on pole multiplicities or a parameter-differentiation assumption.
-/

noncomputable section

open MeasureTheory Set Complex Polynomial

namespace RHTower.WeilHigherDenominator

private lemma log_pow_le_rpow_ge_one (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 1 ≤ u → (Real.log u) ^ k ≤ C * u ^ ε := by
  cases k with
  | zero =>
      refine ⟨1, zero_le_one, fun u hu => ?_⟩
      simpa using Real.one_le_rpow hu hε.le
  | succ k =>
      let δ : ℝ := ε / (k + 1 : ℕ)
      have hδ : 0 < δ := div_pos hε (Nat.cast_pos.mpr (Nat.succ_pos k))
      refine ⟨δ⁻¹ ^ (k + 1), by positivity, fun u hu => ?_⟩
      have hu₀ : 0 < u := zero_lt_one.trans_le hu
      have hp : (u ^ δ) ^ (k + 1 : ℕ) = u ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu₀.le]
        congr 1
        exact div_mul_cancel₀ ε (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      calc
        _ ≤ (u ^ δ / δ) ^ (k + 1) :=
          pow_le_pow_left₀ (Real.log_nonneg hu) (Real.log_le_rpow_div hu₀.le hδ) _
        _ = _ := by rw [div_pow, hp, div_eq_mul_inv, inv_pow]; ring

/-- A uniform two-sided power envelope for every natural logarithmic order. -/
theorem abs_log_pow_le_two_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u →
      |Real.log u| ^ k ≤ C * (u ^ ε + u ^ (-ε)) := by
  obtain ⟨C, hC₀, hC⟩ := log_pow_le_rpow_ge_one k hε
  refine ⟨C, hC₀, fun u hu => ?_⟩
  by_cases hu₁ : 1 ≤ u
  · rw [abs_of_nonneg (Real.log_nonneg hu₁)]
    exact (hC u hu₁).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg hu.le _)) hC₀)
  · have hle : u ≤ 1 := (lt_of_not_ge hu₁).le
    have hinv : 1 ≤ u⁻¹ := by
      rw [← one_div, le_div_iff₀ hu]
      simpa using hle
    have h := hC u⁻¹ hinv
    rw [Real.log_inv, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le,
      ← abs_of_nonpos (Real.log_nonpos hu.le hle)] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg hu.le _)) hC₀)

/-- Multiplying by a real power shifts only the real part of the polar exponent. -/
theorem norm_polarKernel_real_shift (ρ z : ℂ) (δ : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖polarKernel (ρ + (δ : ℂ)) z t‖ = |t| ^ (-δ) * ‖polarKernel ρ z t‖ := by
  have hu : 0 < |t| := abs_pos.mpr ht
  simp only [polarKernel, norm_div, norm_cpow_eq_rpow_re_of_pos hu, neg_re,
    add_re, ofReal_re]
  rw [← mul_div_assoc, ← Real.rpow_add hu]
  congr 2
  ring

/-- The logarithmic moment integrand; its value at zero is immaterial. -/
def logPolarKernel (ρ z : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  (Real.log |t| : ℂ) ^ k * polarKernel ρ z t

theorem measurable_logPolarKernel (ρ z : ℂ) (k : ℕ) :
    Measurable (logPolarKernel ρ z k) := by
  apply Measurable.mul _ (measurable_polarKernel ρ z)
  exact (Complex.measurable_ofReal.comp (Real.measurable_log.comp continuous_abs.measurable)).pow_const k

/-- Every logarithmic order is integrable throughout the same open strip. -/
theorem integrable_logPolarKernel {ρ z : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (hz : 0 < z.im) (k : ℕ) : Integrable (logPolarKernel ρ z k) := by
  let ε : ℝ := min ρ.re (1 - ρ.re) / 2
  have hε : 0 < ε := div_pos (lt_min hρ₀ (sub_pos.mpr hρ₁)) (by norm_num)
  have hε₀ : ε < ρ.re := by dsimp [ε]; linarith [min_le_left ρ.re (1 - ρ.re)]
  have hε₁ : ε < 1 - ρ.re := by dsimp [ε]; linarith [min_le_right ρ.re (1 - ρ.re)]
  obtain ⟨C, hC₀, hC⟩ := abs_log_pow_le_two_rpow k hε
  have hlo : Integrable (polarKernel (ρ + ((-ε : ℝ) : ℂ)) z) :=
    integrable_polarKernel (by simp only [add_re, ofReal_re]; linarith)
      (by simp only [add_re, ofReal_re]; linarith) hz
  have hhi : Integrable (polarKernel (ρ + (ε : ℂ)) z) :=
    integrable_polarKernel (by simp only [add_re, ofReal_re]; linarith)
      (by simp only [add_re, ofReal_re]; linarith) hz
  apply ((hlo.norm.add hhi.norm).const_mul C).mono' (measurable_logPolarKernel ρ z k).aestronglyMeasurable
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [hne] with t ht
  simp only [Pi.add_apply, logPolarKernel, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    norm_polarKernel_real_shift ρ z (-ε) ht, norm_polarKernel_real_shift ρ z ε ht, neg_neg]
  calc
    _ ≤ (C * (|t| ^ ε + |t| ^ (-ε))) * ‖polarKernel ρ z t‖ :=
      mul_le_mul_of_nonneg_right (hC |t| (abs_pos.mpr ht)) (norm_nonneg _)
    _ = _ := by ring

/-- Polynomial logarithmic weights retain absolute convergence, at every degree. -/
theorem integrable_polynomial_polarKernel {ρ z : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1)
    (hz : 0 < z.im) (P : ℂ[X]) :
    Integrable (fun t : ℝ => P.eval (Real.log |t| : ℂ) * polarKernel ρ z t) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Pi.add_def, eval_add, add_mul] using hP.add hQ
  | monomial k c =>
      simpa only [eval_monomial, logPolarKernel, mul_assoc] using
        (integrable_logPolarKernel hρ₀ hρ₁ hz k).const_mul c

/-- The actual logarithmic moments used by the polynomial axis operator. -/
def polarLogMoment (ρ : ℂ) (k : ℕ) : ℂ := ∫ t : ℝ, logPolarKernel ρ I k t

theorem polarLogMoment_zero {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) :
    polarLogMoment ρ 0 = polarAxisFactor ρ := by
  simp only [polarLogMoment, logPolarKernel, pow_zero, one_mul,
    integral_polarKernel_axis hρ₀ hρ₁]

/-- The direct polynomial-weight mode, without derivatives in the exponent. -/
def polynomialPolarMode (ρ : ℂ) (P : ℂ[X]) (z : ℂ) : ℂ :=
  (Real.sqrt z.im : ℂ) * ∫ t : ℝ,
    P.eval (Real.log |t| : ℂ) * polarKernel ρ z t

end RHTower.WeilHigherDenominator
