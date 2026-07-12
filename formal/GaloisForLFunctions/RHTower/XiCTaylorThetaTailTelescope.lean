import GaloisForLFunctions.RHTower.ThetaCuspFourierXi
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor
import GaloisForLFunctions.RHTower.PrimeEnergyZeroTransfer
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Raw even moments of the positive one-sided theta tail. -/
def thetaCuspTailRawEvenMoment (n : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0, x ^ (2 * n) * thetaCuspTailDerivative 0 x

/-- Factorially normalized even moments of the positive one-sided theta tail. -/
def thetaCuspTailEvenCoefficient (n : ℕ) : ℝ :=
  thetaCuspTailRawEvenMoment n / (2 * n).factorial

theorem integrableOn_pow_mul_thetaCuspTailDerivative (k m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * thetaCuspTailDerivative m x) (Ioi 0) := by
  let C := thetaCuspTailDerivativeExpConstant m
  have hbase : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-x)) (Ioi 0) := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hk : (-1 : ℝ) < (k : ℝ) := by linarith
    convert integrableOn_rpow_mul_exp_neg_rpow
      (p := (1 : ℝ)) (s := (k : ℝ)) hk (by norm_num) using 1
    ext x
    rw [Real.rpow_natCast, Real.rpow_one]
  have hdom : IntegrableOn (fun x : ℝ => C * (x ^ k * Real.exp (-x))) (Ioi 0) :=
    hbase.const_mul C
  apply Integrable.mono hdom
  · exact ((continuous_id.pow k).mul
      (differentiable_thetaCuspTailDerivative m).continuous).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have htail := abs_thetaCuspTailDerivative_le_exp_neg m hx0
    dsimp only [C]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx0,
      abs_of_nonneg (thetaCuspTailDerivativeExpConstant_nonneg m),
      abs_of_pos (Real.exp_pos _)]
    calc
      x ^ k * |thetaCuspTailDerivative m x| ≤
          x ^ k * (thetaCuspTailDerivativeExpConstant m * Real.exp (-x)) := by
        gcongr
      _ = thetaCuspTailDerivativeExpConstant m *
          (x ^ k * Real.exp (-x)) := by ring

theorem pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (k m : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * thetaCuspTailDerivative m x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hle : ∀ᶠ x : ℝ in atTop,
      ‖x ^ k * thetaCuspTailDerivative m x‖ ≤
        thetaCuspTailDerivativeExpConstant m * (x ^ k * Real.exp (-x)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have htail := abs_thetaCuspTailDerivative_le_exp_neg m hx
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx]
    calc
      x ^ k * |thetaCuspTailDerivative m x| ≤
          x ^ k * (thetaCuspTailDerivativeExpConstant m * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left htail (pow_nonneg hx k)
      _ = thetaCuspTailDerivativeExpConstant m *
          (x ^ k * Real.exp (-x)) := by ring
  have hmajor : Tendsto
      (fun x : ℝ => thetaCuspTailDerivativeExpConstant m *
        (x ^ k * Real.exp (-x))) atTop (𝓝 0) := by
    simpa using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul
        (thetaCuspTailDerivativeExpConstant m)
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) hle hmajor

theorem pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos
    {k : ℕ} (hk : 0 < k) (m : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * thetaCuspTailDerivative m x)
      (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun x : ℝ => x ^ k * thetaCuspTailDerivative m x) :=
    (continuous_id.pow k).mul (differentiable_thetaCuspTailDerivative m).continuous
  have h := (hc.tendsto 0).mono_left
    (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa [Nat.ne_of_gt hk] using h

theorem integral_pow_mul_thetaCuspTailDerivative_two
    {k : ℕ} (hk : 2 ≤ k) :
    (∫ x : ℝ in Ioi 0, x ^ k * thetaCuspTailDerivative 2 x) =
      (k : ℝ) * (k - 1 : ℕ) *
        ∫ x : ℝ in Ioi 0, x ^ (k - 2) * thetaCuspTailDerivative 0 x := by
  have hk0 : 0 < k := lt_of_lt_of_le (by omega) hk
  have hk1 : 0 < k - 1 := by omega
  have hfirst := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => x ^ k)
    (u' := fun x : ℝ => (k : ℝ) * x ^ (k - 1))
    (v := thetaCuspTailDerivative 1)
    (v' := thetaCuspTailDerivative 2)
    (fun x _ => by simpa [mul_comm] using hasDerivAt_pow k x)
    (fun x _ => hasDerivAt_thetaCuspTailDerivative 1 x)
    (integrableOn_pow_mul_thetaCuspTailDerivative k 2)
    (by
      simpa only [Pi.mul_apply, ← mul_assoc] using
        (integrableOn_pow_mul_thetaCuspTailDerivative (k - 1) 1).const_mul (k : ℝ))
    (pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos hk0 1)
    (pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero k 1)
  have hsecond := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ))
    (u := fun x : ℝ => x ^ (k - 1))
    (u' := fun x : ℝ => ((k - 1 : ℕ) : ℝ) * x ^ (k - 2))
    (v := thetaCuspTailDerivative 0)
    (v' := thetaCuspTailDerivative 1)
    (fun x _ => by
      convert hasDerivAt_pow (k - 1) x using 1)
    (fun x _ => hasDerivAt_thetaCuspTailDerivative 0 x)
    (integrableOn_pow_mul_thetaCuspTailDerivative (k - 1) 1)
    (by
      simpa only [Pi.mul_apply, ← mul_assoc] using
        (integrableOn_pow_mul_thetaCuspTailDerivative (k - 2) 0).const_mul
          ((k - 1 : ℕ) : ℝ))
    (pow_mul_thetaCuspTailDerivative_tendsto_zero_of_pos hk1 0)
    (pow_mul_thetaCuspTailDerivative_tendsto_atTop_zero (k - 1) 0)
  rw [show (fun x : ℝ => ((k : ℝ) * x ^ (k - 1)) *
      thetaCuspTailDerivative 1 x) =
      fun x => (k : ℝ) * (x ^ (k - 1) * thetaCuspTailDerivative 1 x) by
        funext x; ring,
    integral_const_mul] at hfirst
  rw [show (fun x : ℝ => (((k - 1 : ℕ) : ℝ) * x ^ (k - 2)) *
      thetaCuspTailDerivative 0 x) =
      fun x => ((k - 1 : ℕ) : ℝ) *
        (x ^ (k - 2) * thetaCuspTailDerivative 0 x) by
        funext x; ring,
    integral_const_mul] at hsecond
  rw [hsecond] at hfirst
  convert hfirst using 1
  ring

/-- The seam boundary contributes the exceptional constant term in the tail-moment recurrence. -/
theorem thetaCuspRawEvenMoment_zero_eq_tail :
    thetaCuspRawEvenMoment 0 =
      1 / 2 - (1 / 4 : ℝ) * thetaCuspTailRawEvenMoment 0 := by
  have h := integral_Ioi_thetaCuspFullSource_mul_cos 0
  norm_num at h
  rw [thetaCuspRawEvenMoment, thetaCuspTailRawEvenMoment]
  norm_num
  linarith

/-- For positive moment order, two integrations by parts transfer the cusp operator to the
monomial and give a two-step factorial coefficient. -/
theorem thetaCuspRawEvenMoment_succ_eq_tail (n : ℕ) :
    thetaCuspRawEvenMoment (n + 1) =
      ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 1 : ℕ) : ℝ) *
          thetaCuspTailRawEvenMoment n -
        (1 / 4 : ℝ) * thetaCuspTailRawEvenMoment (n + 1) := by
  let k : ℕ := 2 * (n + 1)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hibp := integral_pow_mul_thetaCuspTailDerivative_two hk
  rw [thetaCuspRawEvenMoment, thetaCuspTailRawEvenMoment,
    thetaCuspTailRawEvenMoment]
  have hsource : (fun x : ℝ => x ^ (2 * (n + 1)) * thetaCuspFullSource x) =
      fun x => x ^ (2 * (n + 1)) * thetaCuspTailDerivative 2 x -
        (1 / 4 : ℝ) *
          (x ^ (2 * (n + 1)) * thetaCuspTailDerivative 0 x) := by
    funext x
    rw [thetaCuspFullSource_eq_tail_second_sub]
    ring
  rw [hsource, integral_sub
    (integrableOn_pow_mul_thetaCuspTailDerivative (2 * (n + 1)) 2)
    ((integrableOn_pow_mul_thetaCuspTailDerivative (2 * (n + 1)) 0).const_mul
      (1 / 4 : ℝ)), integral_const_mul]
  rw [show 2 * (n + 1) = 2 * n + 2 by omega]
  have hkEq : k = 2 * n + 2 := by dsimp [k]; omega
  rw [hkEq] at hibp
  have hsub1 : 2 * n + 2 - 1 = 2 * n + 1 := by omega
  have hsub2 : 2 * n + 2 - 2 = 2 * n := by omega
  rw [hsub1, hsub2] at hibp
  rw [hibp]
  ring

/-- Exact factorially normalized coefficient telescope. -/
theorem thetaCuspRawEvenCoefficient_succ_eq_tail (n : ℕ) :
    thetaCuspRawEvenMoment (n + 1) / (2 * (n + 1)).factorial =
      thetaCuspTailEvenCoefficient n -
        (1 / 4 : ℝ) * thetaCuspTailEvenCoefficient (n + 1) := by
  rw [thetaCuspRawEvenMoment_succ_eq_tail,
    thetaCuspTailEvenCoefficient, thetaCuspTailEvenCoefficient]
  have hfac : (2 * (n + 1)).factorial =
      (2 * n).factorial * (2 * n + 1) * (2 * n + 2) := by
    calc
      (2 * (n + 1)).factorial = (2 * n + 2).factorial := by congr 1
      _ = (2 * n + 1).factorial * (2 * n + 2) := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.factorial_succ]
        ring
      _ = ((2 * n).factorial * (2 * n + 1)) * (2 * n + 2) := by
        rw [Nat.factorial_succ]
        ring
  rw [hfac]
  push_cast
  field_simp

theorem thetaCuspRawEvenCoefficient_zero_eq_tail :
    thetaCuspRawEvenMoment 0 / (0 : ℕ).factorial =
      1 / 2 - (1 / 4 : ℝ) * thetaCuspTailEvenCoefficient 0 := by
  rw [thetaCuspRawEvenMoment_zero_eq_tail, thetaCuspTailEvenCoefficient]
  simp [thetaCuspTailRawEvenMoment]

/-- The scalar Cauchy coefficient is the corresponding Xi jet divided by the factorial. -/
theorem cauchyPowerSeries_XiC_coeff (k : ℕ) :
    (cauchyPowerSeries XiC 0 1).coeff k =
      iteratedDeriv k XiC 0 / k.factorial := by
  have hp := (analyticOnNhd_univ_iff_differentiable.mp XiC_analytic).hasFPowerSeriesOnBall
    0 (R := 1) (by norm_num)
  have hfac := hp.factorial_smul (1 : ℂ) k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  change k.factorial • (cauchyPowerSeries XiC 0 1).coeff k =
      iteratedDeriv k XiC 0 at hfac
  have hfac' : (k.factorial : ℂ) * (cauchyPowerSeries XiC 0 1).coeff k =
      iteratedDeriv k XiC 0 := by
    simpa only [nsmul_eq_mul] using hfac
  rw [eq_div_iff (by exact_mod_cast k.factorial_ne_zero)]
  simpa only [mul_comm] using hfac'

/-- The even Cauchy coefficients are the alternating factorially normalized source moments. -/
theorem cauchyPowerSeries_XiC_coeff_two_mul (n : ℕ) :
    (cauchyPowerSeries XiC 0 1).coeff (2 * n) =
      ((((-1 : ℝ) ^ n *
        (thetaCuspRawEvenMoment n / (2 * n).factorial) : ℝ) : ℂ)) := by
  rw [cauchyPowerSeries_XiC_coeff,
    iteratedDeriv_XiC_zero_eq_rawEvenMoment]
  push_cast
  ring

theorem cauchyPowerSeries_XiC_coeff_odd {k : ℕ} (hk : Odd k) :
    (cauchyPowerSeries XiC 0 1).coeff k = 0 := by
  rw [cauchyPowerSeries_XiC_coeff, iteratedDeriv_XiC_odd_zero hk, zero_div]

/-- The magnitude polynomial of the first `d+1` even Xi Taylor coefficients in `w=-z²`. -/
def xiCTaylorEvenMagnitudePolynomial (d : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    C (thetaCuspRawEvenMoment k / (2 * k).factorial) * X ^ k

/-- The corresponding tail-moment polynomial. -/
def thetaCuspTailEvenPolynomial (d : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (d + 1), C (thetaCuspTailEvenCoefficient k) * X ^ k

theorem xiCTaylorEvenMagnitudePolynomial_succ_add (d : ℕ) :
    xiCTaylorEvenMagnitudePolynomial (d + 1) =
      xiCTaylorEvenMagnitudePolynomial d +
        C (thetaCuspRawEvenMoment (d + 1) / (2 * (d + 1)).factorial) * X ^ (d + 1) := by
  simp [xiCTaylorEvenMagnitudePolynomial, Finset.sum_range_succ]

theorem thetaCuspTailEvenPolynomial_succ_add (d : ℕ) :
    thetaCuspTailEvenPolynomial (d + 1) =
      thetaCuspTailEvenPolynomial d +
        C (thetaCuspTailEvenCoefficient (d + 1)) * X ^ (d + 1) := by
  simp [thetaCuspTailEvenPolynomial, Finset.sum_range_succ]

theorem xiCTaylorEvenMagnitudePolynomial_zero :
    xiCTaylorEvenMagnitudePolynomial 0 =
      C (1 / 2 - (1 / 4 : ℝ) * thetaCuspTailEvenCoefficient 0) := by
  rw [xiCTaylorEvenMagnitudePolynomial]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one]
  rw [thetaCuspRawEvenMoment_zero_eq_tail]
  norm_num [thetaCuspTailEvenCoefficient]

/-- **Finite theta-tail coefficient telescope.**  The first `d+2` canonical even Xi Taylor
coefficient magnitudes are obtained by multiplying the first `d+1` tail-moment section by
`X-1/4`, adding the seam constant, and retaining one explicit top defect. -/
theorem xiCTaylorEvenMagnitudePolynomial_succ (d : ℕ) :
    xiCTaylorEvenMagnitudePolynomial (d + 1) =
      C (1 / 2) + (X - C (1 / 4)) * thetaCuspTailEvenPolynomial d -
        C ((1 / 4 : ℝ) * thetaCuspTailEvenCoefficient (d + 1)) * X ^ (d + 1) := by
  induction d with
  | zero =>
      rw [xiCTaylorEvenMagnitudePolynomial_succ_add,
        xiCTaylorEvenMagnitudePolynomial_zero,
        thetaCuspRawEvenCoefficient_succ_eq_tail]
      simp [thetaCuspTailEvenPolynomial]
      ring
  | succ d ih =>
      rw [xiCTaylorEvenMagnitudePolynomial_succ_add, ih,
        thetaCuspRawEvenCoefficient_succ_eq_tail,
        thetaCuspTailEvenPolynomial_succ_add]
      simp only [C_sub, C_mul]
      ring

/-- Evaluation form of the telescope coordinate: the canonical Xi Taylor section through even
order `2d` is the even-magnitude polynomial evaluated at `w=-z²`. -/
theorem xiCTaylorApprox_oddCutoff_eq_evenMagnitude_eval (d : ℕ) (z : ℂ) :
    xiCTaylorApprox (2 * d + 1) z =
      (xiCTaylorEvenMagnitudePolynomial d).eval₂ (algebraMap ℝ ℂ) (-z ^ 2) := by
  induction d with
  | zero =>
      unfold xiCTaylorApprox FormalMultilinearSeries.partialSum
      simp [xiCTaylorEvenMagnitudePolynomial]
      rw [cauchyPowerSeries_XiC_coeff_two_mul 0]
      norm_num
  | succ d ih =>
      rw [show 2 * (d + 1) + 1 = (2 * d + 1) + 2 by omega]
      unfold xiCTaylorApprox FormalMultilinearSeries.partialSum at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [show 2 * d + 1 + 1 = 2 * (d + 1) by omega]
      have hodd : Odd (2 * d + 1) := ⟨d, by omega⟩
      rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        FormalMultilinearSeries.apply_eq_pow_smul_coeff,
        cauchyPowerSeries_XiC_coeff_odd hodd,
        cauchyPowerSeries_XiC_coeff_two_mul]
      rw [xiCTaylorEvenMagnitudePolynomial_succ_add, eval₂_add, eval₂_mul,
        eval₂_C, eval₂_pow, ih]
      push_cast
      simp [eval₂_X, pow_succ]
      ring

end
end RHTower
