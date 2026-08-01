import GaloisForLFunctions.HTGeometry.DigammaFieldLexRatio
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Gamma dominates every algebraic-logarithmic factor

On the vertical line `Re s = 1/2 + m` the corpus's two-sided modulus bounds give
`‖Γ(s)‖ ≤ C |t|^m e^{-π|t|/2}`, so any positive power of `Γ` decays exponentially while a power of
the argument and a power of the leading logarithm grow at most polynomially.

Hence `Γ^j · s^k · L^b → 0` for every `j ≥ 1`, and the same with the digamma in place of its leading
logarithm.  This is the analytic form of the exponential valuation direction created by adjoining
`Γ`: in the projective boundary of `ℂ(s)⟨Γ⟩` the `Γ`-exponent dominates the polynomial and
logarithmic data.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- A polynomial factor is beaten by a decaying exponential. -/
theorem tendsto_pow_mul_exp_neg_scaled {c : ℝ} (hc : 0 < c) (N : ℕ) :
    Tendsto (fun t : ℝ => t ^ N * Real.exp (-(c * t))) atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hscale : Tendsto (fun t : ℝ => c * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc tendsto_id
  have hcomp := hbase.comp hscale
  have hmul := hcomp.const_mul ((c ^ N)⁻¹)
  rw [mul_zero] at hmul
  refine hmul.congr fun t => ?_
  simp only [Function.comp_apply, mul_pow]
  field_simp

/-- The vertical line `Re s = 1/2 + m` in the two coordinate shapes. -/
theorem line_eq (m : ℕ) (t : ℝ) :
    (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 1 / 2 + (t : ℂ) * Complex.I + (m : ℂ) := by
  push_cast
  ring

/-- **`Γ` beats every polynomial and logarithmic factor on a vertical line.** -/
theorem tendsto_gamma_pow_mul_vertical (m : ℕ) {j : ℕ} (hj : 0 < j) (k b : ℕ) :
    Tendsto (fun t : ℝ =>
      Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ j
        * (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ k * (vertLog t) ^ b) atTop (nhds 0) := by
  set C₁ : ℝ := Real.sqrt (2 * Real.pi) * ((3 : ℝ) / 2 + m) ^ m with hC₁
  set C₂ : ℝ := (3 : ℝ) / 2 + m with hC₂
  set C₃ : ℝ := 1 + Real.pi / 2 with hC₃
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    positivity
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ j
        * (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ k * (vertLog t) ^ b‖
        ≤ (C₁ ^ j * C₂ ^ k * C₃ ^ b) * (t ^ (m * j + k + b) * Real.exp (-(Real.pi * j / 2 * t))) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have habs : |t| = t := abs_of_nonneg (by linarith)
    have hlog : Real.log t ≤ t := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < t)
      linarith
    have hlognn : 0 ≤ Real.log t := Real.log_nonneg ht
    -- the Gamma factor
    have hΓ : ‖Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C₁ * t ^ m * Real.exp (-(Real.pi * t / 2)) := by
      have h := (GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_nat_bounds m
        (by rw [habs]; exact ht)).2
      rw [← line_eq m t, habs] at h
      calc ‖Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ Real.sqrt (2 * Real.pi) * (((3 : ℝ) / 2 + m) * t) ^ m
              * Real.exp (-(Real.pi * t / 2)) := h
        _ = C₁ * t ^ m * Real.exp (-(Real.pi * t / 2)) := by
            rw [hC₁, mul_pow]
            ring
    -- the argument factor
    have hs : ‖(((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₂ * t := by
      have hre : (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 + m := by simp
      have him : (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      calc ‖(((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ |(((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I).re|
            + |(((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = (1 / 2 + m) + t := by
            rw [hre, him, abs_of_nonneg (by positivity), abs_of_nonneg (by linarith)]
        _ ≤ C₂ * t := by
            rw [hC₂]
            nlinarith [ht, Nat.cast_nonneg (α := ℝ) m]
    -- the logarithm factor
    have hL : ‖vertLog t‖ ≤ C₃ * t := by
      have h := norm_vertLog_le ht
      rw [hC₃]
      nlinarith [ht, Real.pi_pos]
    have hΓnn : (0:ℝ) ≤ ‖Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
      norm_nonneg _
    rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow]
    have h1 : ‖Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ j
        ≤ (C₁ * t ^ m * Real.exp (-(Real.pi * t / 2))) ^ j := pow_le_pow_left₀ hΓnn hΓ j
    have h2 : ‖(((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ k ≤ (C₂ * t) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) hs k
    have h3 : ‖vertLog t‖ ^ b ≤ (C₃ * t) ^ b := pow_le_pow_left₀ (norm_nonneg _) hL b
    have hexp : (Real.exp (-(Real.pi * t / 2))) ^ j = Real.exp (-(Real.pi * j / 2 * t)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    calc ‖Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ j
          * ‖(((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ k * ‖vertLog t‖ ^ b
        ≤ (C₁ * t ^ m * Real.exp (-(Real.pi * t / 2))) ^ j * (C₂ * t) ^ k * (C₃ * t) ^ b := by
          gcongr
      _ = (C₁ ^ j * C₂ ^ k * C₃ ^ b)
            * (t ^ (m * j + k + b) * Real.exp (-(Real.pi * j / 2 * t))) := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, hexp, pow_add, pow_add]
          ring
  refine squeeze_zero_norm' hbound ?_
  have hjpos : 0 < Real.pi * j / 2 := by
    have : (0:ℝ) < (j : ℝ) := by exact_mod_cast hj
    positivity
  have := (tendsto_pow_mul_exp_neg_scaled hjpos (m * j + k + b)).const_mul (C₁ ^ j * C₂ ^ k * C₃ ^ b)
  rw [mul_zero] at this
  exact this

/-- The same domination with the digamma in place of its leading logarithm. -/
theorem tendsto_gamma_pow_mul_digamma_vertical (m : ℕ) {j : ℕ} (hj : 0 < j) (k b : ℕ) :
    Tendsto (fun t : ℝ =>
      Complex.Gamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ j
        * (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ k
        * Complex.digamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) ^ b)
      atTop (nhds 0) := by
  have hσ : (0 : ℝ) ≤ 1 / 2 + m := by positivity
  have hquot : Tendsto (fun t : ℝ =>
      (Complex.digamma (((1 / 2 + m : ℝ) : ℂ) + (t : ℂ) * Complex.I) / vertLog t) ^ b)
      atTop (nhds 1) := by
    have h := (tendsto_digamma_div_vertLog hσ).pow b
    rwa [one_pow] at h
  have hprod := (tendsto_gamma_pow_mul_vertical m hj k b).mul hquot
  rw [zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero] with t ht
  rw [div_pow]
  field_simp

/-- `Γ` does not vanish on a vertical line above the real axis. -/
theorem eventually_gamma_ne_zero (m : ℕ) :
    ∀ᶠ t : ℝ in atTop,
      Complex.Gamma (linePt m t) ≠ 0 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  refine Complex.Gamma_ne_zero fun n => ?_
  intro hcon
  have him : (linePt m t).im = t := by simp [linePt]
  rw [hcon] at him
  simp only [Complex.neg_im, Complex.natCast_im, neg_zero] at him
  linarith [him]

end GaloisForLFunctions
