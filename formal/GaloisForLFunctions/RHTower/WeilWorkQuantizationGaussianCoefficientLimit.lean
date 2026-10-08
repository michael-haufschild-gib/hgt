import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianRecovery
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Recovery of each actual centered coefficient

A single absolute-line majorant controls every Gaussian scale T>=1.
The boundary Fourier moment therefore recovers each literal coefficient,
without an assumed limiting physical mean or boundary Dirichlet expansion.
-/

open Complex Set Filter MeasureTheory Topology
noncomputable section
namespace RHTower.WeilSpectral
variable {lam : ℕ → ℝ}

theorem norm_quantizationCenteredGaussianCoeff_le (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) (ℓ : ℝ) (n : ℕ) :
    ‖quantizationCenteredGaussianCoeff hW T ℓ n‖ ≤
      Real.exp (ℓ + 1) * ‖LSeries.term (quantizationCenteredCoeff hW) (3 / 2) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [quantizationCenteredGaussianCoeff]
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hTs : 1 ≤ T ^ 2 := by nlinarith
  have he : -Real.log (n : ℝ) / 2 - (T * (ℓ - Real.log (n : ℝ))) ^ 2 / 4 ≤
      ℓ + 1 - Real.log (n : ℝ) * (3 / 2) := by
    nlinarith [sq_nonneg (ℓ - Real.log (n : ℝ) + 2),
      mul_nonneg (sub_nonneg.mpr hTs) (sq_nonneg (ℓ - Real.log (n : ℝ)))]
  have hr : (-(Real.log (n : ℝ) : ℂ) / 2).re = -Real.log (n : ℝ) / 2 := by norm_cast
  have hs : (3 / 2 : ℂ).re = (3 / 2 : ℝ) := by norm_num
  rw [quantizationCenteredGaussianCoeff, norm_mul, norm_mul, Complex.norm_exp,
    Complex.norm_exp, hr]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [LSeries.norm_term_eq, if_neg hn, hs]
  rw [Real.rpow_def_of_pos hnR]
  calc
    _ = ‖quantizationCenteredCoeff hW n‖ * Real.exp
        (-Real.log (n : ℝ) / 2 - (T * (ℓ - Real.log (n : ℝ))) ^ 2 / 4) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
    _ ≤ ‖quantizationCenteredCoeff hW n‖ * Real.exp
        (ℓ + 1 - Real.log (n : ℝ) * (3 / 2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)
    _ = _ := by rw [Real.exp_sub]; ring

private theorem coefficient_limit (hW : WeilPositiveFull lam) {n : ℕ} (hn : 0 < n) (m : ℕ) :
    Tendsto (fun T : ℝ => quantizationCenteredGaussianCoeff hW T (Real.log (n : ℝ)) m)
      atTop (𝓝 (if m = n then quantizationCenteredCoeff hW n *
        Complex.exp (-(Real.log (n : ℝ) : ℂ) / 2) else 0)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp only [quantizationCenteredGaussianCoeff, quantizationCenteredCoeff_zero,
      zero_mul, if_neg hn.ne]
    exact tendsto_const_nhds
  by_cases hmn : m = n
  · subst m
    simp only [quantizationCenteredGaussianCoeff, sub_self, mul_zero, zero_pow (by omega : 2 ≠ 0),
      zero_div, neg_zero, ofReal_zero, Complex.exp_zero, mul_one, if_true]
    exact tendsto_const_nhds
  have hl : Real.log (n : ℝ) - Real.log (m : ℝ) ≠ 0 := by
    intro h
    have hn0 : (n : ℝ) ∈ Ioi 0 := by change 0 < (n : ℝ); exact_mod_cast hn
    have hm0 : (m : ℝ) ∈ Ioi 0 := by change 0 < (m : ℝ); exact_mod_cast (Nat.pos_of_ne_zero hm)
    have he := Real.log_injOn_pos hn0 hm0 (sub_eq_zero.mp h)
    have hnm : n = m := by exact_mod_cast he
    exact hmn hnm.symm
  have hq : Tendsto (fun T : ℝ =>
      ((Real.log (n : ℝ) - Real.log (m : ℝ)) ^ 2 / 4) * T ^ 2) atTop atTop :=
    tendsto_const_mul_pow_atTop (by decide) (by positivity)
  have hz := (Complex.continuous_ofReal.tendsto 0).comp
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp hq)
  have he (T : ℝ) : Complex.exp (-((T * (Real.log (n : ℝ) - Real.log (m : ℝ))) ^ 2 / 4 : ℝ)) =
      (Real.exp (-(((Real.log (n : ℝ) - Real.log (m : ℝ)) ^ 2 / 4) * T ^ 2)) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp only [if_neg hmn]
  simpa only [quantizationCenteredGaussianCoeff, he, Function.comp_def,
    Complex.ofReal_zero, mul_zero] using
    hz.const_mul (quantizationCenteredCoeff hW m * Complex.exp (-(Real.log (m : ℝ) : ℂ) / 2))

private theorem exp_neg_log_half {n : ℕ} (hn : 0 < n) :
    Complex.exp (-(Real.log (n : ℝ) : ℂ) / 2) = (Real.sqrt (n : ℝ) : ℂ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have he : -(Real.log (n : ℝ) : ℂ) / 2 = ((-(Real.log (n : ℝ) / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp, Real.exp_neg, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hnR, ← Complex.ofReal_inv]
  congr 2
  congr 1
  ring

/-- Every normalized physical Gaussian moment recovers its actual centered Dirichlet coefficient. -/
theorem tendsto_quantizationCenteredGaussianMoment (hW : WeilPositiveFull lam)
    {n : ℕ} (hn : 0 < n) :
    Tendsto (fun T : ℝ => quantizationCenteredGaussianMoment hW T (Real.log (n : ℝ)))
      atTop (𝓝 (quantizationCenteredCoeff hW n / (Real.sqrt (n : ℝ) : ℂ))) := by
  have ha := quantizationCenteredCoeff_summable hW (s := 3 / 2) (by norm_num)
  have hh := tendsto_tsum_of_dominated_convergence
    (ha.norm.mul_left (Real.exp (Real.log (n : ℝ) + 1))) (coefficient_limit hW hn) (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT m
      exact norm_quantizationCenteredGaussianCoeff_le hW hT _ m)
  simp only [tsum_ite_eq, exp_neg_log_half hn, ← div_eq_mul_inv] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  exact (quantizationCenteredGaussianMoment_eq_tsum hW hT _).symm

end RHTower.WeilSpectral
