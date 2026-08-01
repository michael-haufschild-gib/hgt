import GaloisForLFunctions.HTGeometry.GammaVerticalPolynomialDecay
import GaloisForLFunctions.HTGeometry.GammaVerticalSuperPolynomialDecay

/-!
# The exponential valuation direction on an arbitrary vertical line

`Γ` decays faster than any polynomial on every vertical line of the right half plane, and it is
bounded there by `Γ(σ)`.  Splitting off one factor of `Γ` from a positive power therefore dominates
any polynomial factor in the argument and any power of the leading logarithm — or of the digamma,
which is asymptotic to it.

These are the general-`σ` forms of the domination results previously available only on the
half-integer lines.
-/

open MeasureTheory Filter Set Real Complex

namespace GaloisForLFunctions

/-- **`Γ` beats every polynomial and logarithmic factor on every vertical line.** -/
theorem tendsto_gamma_pow_mul_vertical_general {σ : ℝ} (hσ : 0 < σ) {j : ℕ} (hj : 0 < j)
    (k b : ℕ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
      * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * (vertLog t) ^ b) atTop (nhds 0) := by
  set M : ℝ := Real.Gamma σ with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact le_of_lt (Real.Gamma_pos_of_pos hσ)
  set C₂ : ℝ := σ + 1 with hC₂
  set C₃ : ℝ := 1 + Real.pi / 2 with hC₃
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
        * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k * (vertLog t) ^ b‖
        ≤ (C₂ ^ k * C₃ ^ b * M ^ (j - 1))
          * ‖(t : ℂ) ^ (k + b) * Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) ≤ t := by linarith
    have hlog : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < t)
      linarith
    have hΓb : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M := by
      have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      have h := norm_Gamma_le_real_Gamma_re (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact hσ)
      rwa [hre] at h
    have hs : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₂ * t := by
      have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
      have him : (((σ : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
      calc ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ |(((σ : ℂ) + (t : ℂ) * Complex.I)).re| + |(((σ : ℂ) + (t : ℂ) * Complex.I)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = σ + t := by rw [hre, him, abs_of_pos hσ, abs_of_nonneg ht0]
        _ ≤ C₂ * t := by
            rw [hC₂]
            nlinarith
    have hL : ‖vertLog t‖ ≤ C₃ * t := by
      have h := norm_vertLog_le ht
      rw [hC₃]
      nlinarith [Real.pi_pos]
    obtain ⟨j', hj'⟩ : ∃ j' : ℕ, j = j' + 1 := ⟨j - 1, by omega⟩
    have hjj : j - 1 = j' := by omega
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht0, hjj, hj', pow_succ]
    have h1 : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j' ≤ M ^ j' :=
      pow_le_pow_left₀ (norm_nonneg _) hΓb j'
    have h2 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ k ≤ (C₂ * t) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hs k
    have h3 : ‖vertLog t‖ ^ b ≤ (C₃ * t) ^ b := pow_le_pow_left₀ (norm_nonneg _) hL b
    calc ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j'
            * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            * ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ k * ‖vertLog t‖ ^ b
        ≤ M ^ j' * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (C₂ * t) ^ k
            * (C₃ * t) ^ b := by
          gcongr
      _ = C₂ ^ k * C₃ ^ b * M ^ j'
            * (t ^ (k + b) * ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
          rw [mul_pow, mul_pow, pow_add]
          ring
  refine squeeze_zero_norm' hbound ?_
  have hdecay := tendsto_pow_mul_Gamma_vertical hσ (k + b)
  rw [tendsto_zero_iff_norm_tendsto_zero] at hdecay
  have := hdecay.const_mul (C₂ ^ k * C₃ ^ b * M ^ (j - 1))
  rw [mul_zero] at this
  exact this

/-- The same domination with the digamma in place of its leading logarithm. -/
theorem tendsto_gamma_pow_mul_digamma_vertical_general {σ : ℝ} (hσ : 0 < σ) {j : ℕ} (hj : 0 < j)
    (k b : ℕ) :
    Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
      * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k
      * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ b) atTop (nhds 0) := by
  have hquot : Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t) ^ b) atTop (nhds 1) := by
    have h := (tendsto_digamma_div_vertLog (le_of_lt hσ)).pow b
    rwa [one_pow] at h
  have hprod := (tendsto_gamma_pow_mul_vertical_general hσ hj k b).mul hquot
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero] with t ht
  rw [div_pow]
  field_simp

end GaloisForLFunctions
