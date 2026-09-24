import GaloisForLFunctions.RHTower.EstermannConvexityExplicit
import GaloisForLFunctions.RHTower.EstermannSmoothedSum
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# The smoothed-sum error, explicit in the modulus

The error term of the smoothed twisted divisor sum is the critical-line integral of
`x^{−s} Γ(s) D(s, a/q)`.  Its modulus at `x = 1` is `‖Γ(1/2+iv)‖ ‖D(1/2+iv, a/q)‖`, and both factors
are now explicit: `‖Γ(1/2+iv)‖ ≤ √(2π) e^{−π|v|/2}` and, by the convexity bound,
`‖D(1/2+iv, a/q)‖ ≤ C q^{3/2} (1+|v|)³`.  The product is integrable with an absolute integral, so

`‖error(x)‖ ≤ C' q^{3/2} x^{−1/2}`,  `C'` absolute.

This is the modulus-uniform error the shifted divisor correlation needs: summing the progression law
over the moduli `k` of `∑_n d(n) d(n+h) e^{−nx} = ∑_k ∑_{n ≡ −h (k)} d(n) e^{−nx}` now has a rate.
-/

open Complex MeasureTheory

namespace RHTower

noncomputable section

/-- The absolute weight integral of the critical line. -/
def estermannGammaWeight : ℝ :=
  ∫ v : ℝ, (1 + |v|) ^ (3 : ℕ) * Real.exp (-(Real.pi / 2) * |v|)

theorem integrable_estermannGammaWeight :
    Integrable (fun v : ℝ => (1 + |v|) ^ (3 : ℕ) * Real.exp (-(Real.pi / 2) * |v|)) := by
  have h0 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0
    (show (0 : ℝ) < Real.pi / 2 by positivity)
  have h1 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1
    (show (0 : ℝ) < Real.pi / 2 by positivity)
  have h2 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2
    (show (0 : ℝ) < Real.pi / 2 by positivity)
  have h3 := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 3
    (show (0 : ℝ) < Real.pi / 2 by positivity)
  have hsum := ((h0.const_mul 1).add (h1.const_mul 3)).add ((h2.const_mul 3).add (h3.const_mul 1))
  refine hsum.congr ?_
  filter_upwards with v
  simp only [Pi.add_apply]
  ring

theorem estermannGammaWeight_nonneg : 0 ≤ estermannGammaWeight := by
  refine integral_nonneg (fun v => ?_)
  positivity

/-- The absolute constant of the explicit error bound. -/
def estermannSmoothedErrorConstant : ℝ :=
  (1 / (2 * Real.pi)) * (Real.sqrt (2 * Real.pi) * estermannCriticalLineConstant *
    estermannGammaWeight)

theorem estermannSmoothedErrorConstant_nonneg : 0 ≤ estermannSmoothedErrorConstant := by
  rw [estermannSmoothedErrorConstant]
  have h1 : 0 ≤ estermannCriticalLineConstant := by
    rw [estermannCriticalLineConstant]
    have := estermannStripConstant_nonneg
    positivity
  have h2 := estermannGammaWeight_nonneg
  positivity

/-- The critical-line integrand at `x = 1`, bounded explicitly in the modulus. -/
theorem norm_estermannMellinIntegrand_one_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (v : ℝ) :
    ‖estermannMellinIntegrand q ((a : ZMod q)) 1 (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ (Real.sqrt (2 * Real.pi) * estermannCriticalLineConstant) * (q : ℝ) ^ ((3 : ℝ) / 2) *
        ((1 + |v|) ^ (3 : ℕ) * Real.exp (-(Real.pi / 2) * |v|)) := by
  have hGamma : ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|) := by
    have h := (GaloisForLFunctions.HTGeometry.norm_Gamma_half_add_I_bounds v).2
    have hcast : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hcast]
    have hexp : Real.exp (-(Real.pi * |v| / 2)) = Real.exp (-(Real.pi / 2) * |v|) := by
      congr 1
      ring
    rwa [hexp] at h
  have hD := norm_estermannZeta_critical_line_le q a v
  have hGnn : (0 : ℝ) ≤ ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ := norm_nonneg _
  have hDnn : (0 : ℝ) ≤ ‖estermannZeta q ((a : ZMod q)) (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ :=
    norm_nonneg _
  have hprod := mul_le_mul hGamma hD hDnn (by positivity)
  have hshape : (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi / 2) * |v|)) *
      (estermannCriticalLineConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * (1 + |v|) ^ (3 : ℕ))
      = (Real.sqrt (2 * Real.pi) * estermannCriticalLineConstant) * (q : ℝ) ^ ((3 : ℝ) / 2) *
        ((1 + |v|) ^ (3 : ℕ) * Real.exp (-(Real.pi / 2) * |v|)) := by ring
  rw [estermannMellinIntegrand]
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul, norm_mul]
  rw [← hshape]
  exact hprod

/-- **The explicit error bound.**  `‖error(x)‖ ≤ C q^{3/2} x^{−1/2}` with `C` absolute. -/
theorem norm_estermann_smoothed_error_le (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ} (hx : 0 < x) :
    ‖(1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ,
        estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ estermannSmoothedErrorConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
  have hbase : Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) 1 (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    integrable_estermannMellinIntegrand_vertical q a one_pos (by norm_num) (by norm_num)
      (by norm_num)
  have hint : Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    integrable_estermannMellinIntegrand_vertical q a hx (by norm_num) (by norm_num) (by norm_num)
  set B : ℝ := Real.sqrt (2 * Real.pi) * estermannCriticalLineConstant with hB
  have hB0 : 0 ≤ B := by
    rw [hB, estermannCriticalLineConstant]
    have := estermannStripConstant_nonneg
    positivity
  have hq32 : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := by
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have := Nat.pos_of_ne_zero (NeZero.ne q)
      exact_mod_cast this
    exact (Real.rpow_pos_of_pos hq0 _).le
  -- the integral at `x = 1`
  have hC₀ : (∫ v : ℝ, ‖estermannMellinIntegrand q ((a : ZMod q)) 1
        (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖)
      ≤ B * (q : ℝ) ^ ((3 : ℝ) / 2) * estermannGammaWeight := by
    have hmaj : Integrable (fun v : ℝ => B * (q : ℝ) ^ ((3 : ℝ) / 2) *
        ((1 + |v|) ^ (3 : ℕ) * Real.exp (-(Real.pi / 2) * |v|))) :=
      integrable_estermannGammaWeight.const_mul _
    have hle := integral_mono hbase.norm hmaj (norm_estermannMellinIntegrand_one_le q a)
    refine hle.trans ?_
    rw [estermannGammaWeight, ← integral_const_mul]
  -- scaling in `x`
  have hxpow : (0 : ℝ) < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hscale : ∀ v : ℝ,
      ‖estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
        = x ^ (-(1 / 2 : ℝ)) *
          ‖estermannMellinIntegrand q ((a : ZMod q)) 1 (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
    intro v
    have hre : (-(((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
    simp only [estermannMellinIntegrand, norm_mul, Complex.ofReal_one, Complex.one_cpow,
      one_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    ring
  have hnorm : ‖∫ v : ℝ,
      estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ x ^ (-(1 / 2 : ℝ)) * (B * (q : ℝ) ^ ((3 : ℝ) / 2) * estermannGammaWeight) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have heq : (∫ v : ℝ, ‖estermannMellinIntegrand q ((a : ZMod q)) x
          (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖)
        = x ^ (-(1 / 2 : ℝ)) * ∫ v : ℝ, ‖estermannMellinIntegrand q ((a : ZMod q)) 1
          (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hscale)
    rw [heq]
    exact mul_le_mul_of_nonneg_left hC₀ hxpow.le
  rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ,
        estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) *
          (x ^ (-(1 / 2 : ℝ)) * (B * (q : ℝ) ^ ((3 : ℝ) / 2) * estermannGammaWeight)) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = estermannSmoothedErrorConstant * (q : ℝ) ^ ((3 : ℝ) / 2) * x ^ (-(1 / 2 : ℝ)) := by
        rw [estermannSmoothedErrorConstant, hB]
        ring

end

end RHTower
