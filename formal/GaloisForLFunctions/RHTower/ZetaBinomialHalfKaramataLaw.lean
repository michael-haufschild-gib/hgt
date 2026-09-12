import GaloisForLFunctions.RHTower.ZetaBinomialHalfFractionalPole
import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.HTGeometry.ExponentialCompactification
import GaloisForLFunctions.HTGeometry.GammaHalfLaplace

/-!
# Karamata scaling law of the positive zeta half

The nonnegative coefficients of the Dirichlet square root of zeta define, at abscissa `1 + t`,
a probability law on the scaled logarithmic coordinates `t * log n`.  Its `k`-th Laplace moment
is the exact quotient

`B(1 + (k + 1)t) / B(1 + t)`.

The square-root pole `sqrt(t) B(1+t) → 1` therefore forces convergence of every natural
Laplace moment to `1 / sqrt(k + 1)`, the transform of the unit-rate Gamma law of shape `1 / 2`.
Exponential compactification and the Hausdorff moment theorem then give unconditional weak
convergence of the compactified laws.  This is a real-axis Tauberian input; it does not continue
the Dirichlet square root across `Re s = 1`.
-/

open ArithmeticFunction Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ArithmeticFunction.zeta ComplexOrder ENNReal NNReal

noncomputable section

namespace RHTower

/-- Real nonnegative coefficients of the positive Dirichlet square root of zeta. -/
def zetaBinomialHalfReal (n : ℕ) : ℝ := (zetaBinomialHalf n).re

@[simp] theorem zetaBinomialHalfReal_zero : zetaBinomialHalfReal 0 = 0 := by
  simp [zetaBinomialHalfReal]

@[simp] theorem zetaBinomialHalfReal_one : zetaBinomialHalfReal 1 = 1 := by
  simp [zetaBinomialHalfReal]

theorem zetaBinomialHalfReal_nonneg (n : ℕ) : 0 ≤ zetaBinomialHalfReal n :=
  zetaBinomialHalf_apply_nonneg n

theorem ofReal_zetaBinomialHalfReal :
    (fun n : ℕ => ((zetaBinomialHalfReal n : ℝ) : ℂ)) = zetaBinomialHalf := by
  funext n
  apply Complex.ext
  · simp [zetaBinomialHalfReal]
  · simp [zetaBinomialHalf_apply_im]

/-- Positive zeta-half mass at the real abscissa `1 + t`. -/
def zetaBinomialHalfDirichletMass (t : ℝ) : ℝ :=
  ∑' n : ℕ, zetaBinomialHalfReal n * (n : ℝ) ^ (-(1 + t))

theorem summable_zetaBinomialHalfDirichletTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => zetaBinomialHalfReal n * (n : ℝ) ^ (-(1 + t))) := by
  apply GaloisForLFunctions.HTGeometry.summable_real_of_lseriesSummable
    zetaBinomialHalfReal_zero
  rw [ofReal_zetaBinomialHalfReal]
  exact LSeriesSummable_zetaBinomialHalf (by simpa using ht)

theorem zetaBinomialHalfDirichletMass_eq_LSeries_re {t : ℝ} :
    zetaBinomialHalfDirichletMass t =
      (LSeries zetaBinomialHalf ((1 + t : ℝ) : ℂ)).re := by
  have h := GaloisForLFunctions.HTGeometry.ofReal_tsum_eq_lseries
    (f := zetaBinomialHalfReal) zetaBinomialHalfReal_zero (σ := 1 + t)
  rw [ofReal_zetaBinomialHalfReal] at h
  have hre := congrArg Complex.re h
  simpa [zetaBinomialHalfDirichletMass] using hre

theorem zetaBinomialHalfDirichletMass_pos {t : ℝ} (ht : 0 < t) :
    0 < zetaBinomialHalfDirichletMass t := by
  have hs := summable_zetaBinomialHalfDirichletTerm ht
  have hle := hs.le_tsum 1 (fun n _ =>
    mul_nonneg (zetaBinomialHalfReal_nonneg n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  refine zero_lt_one.trans_le ?_
  rw [zetaBinomialHalfDirichletMass]
  simpa only [Nat.cast_one, Real.one_rpow, zetaBinomialHalfReal_one, one_mul] using hle

/-- Normalized positive Dirichlet weight at distance `t` from the pole. -/
def zetaBinomialHalfKaramataWeight (t : ℝ) (n : ℕ) : ℝ :=
  zetaBinomialHalfReal n * (n : ℝ) ^ (-(1 + t)) /
    zetaBinomialHalfDirichletMass t

theorem zetaBinomialHalfKaramataWeight_nonneg {t : ℝ} (ht : 0 < t) (n : ℕ) :
    0 ≤ zetaBinomialHalfKaramataWeight t n :=
  div_nonneg
    (mul_nonneg (zetaBinomialHalfReal_nonneg n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (zetaBinomialHalfDirichletMass_pos ht).le

theorem summable_zetaBinomialHalfKaramataWeight {t : ℝ} (ht : 0 < t) :
    Summable (zetaBinomialHalfKaramataWeight t) := by
  exact (summable_zetaBinomialHalfDirichletTerm ht).div_const _

theorem tsum_zetaBinomialHalfKaramataWeight {t : ℝ} (ht : 0 < t) :
    ∑' n : ℕ, zetaBinomialHalfKaramataWeight t n = 1 := by
  rw [show zetaBinomialHalfKaramataWeight t = fun n : ℕ =>
      (zetaBinomialHalfReal n * (n : ℝ) ^ (-(1 + t))) /
        zetaBinomialHalfDirichletMass t by rfl]
  rw [tsum_div_const]
  exact div_self (zetaBinomialHalfDirichletMass_pos ht).ne'

/-- Karamata coordinate: distance from the pole times logarithmic arithmetic height. -/
def zetaBinomialHalfKaramataLogCoordinate (t : ℝ) (n : ℕ) : ℝ :=
  t * Real.log n

/-- Raw positive zeta-half law, used on `t > 0`. -/
def zetaBinomialHalfKaramataLawRaw (t : ℝ) : Measure ℝ :=
  GaloisForLFunctions.HTGeometry.weightedPointLaw
    (zetaBinomialHalfKaramataLogCoordinate t)
    (fun n : ℕ => ENNReal.ofReal (zetaBinomialHalfKaramataWeight t n))

theorem isProbabilityMeasure_zetaBinomialHalfKaramataLawRaw {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (zetaBinomialHalfKaramataLawRaw t) := by
  refine GaloisForLFunctions.HTGeometry.isProbabilityMeasure_weightedPointLaw _ _ ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (zetaBinomialHalfKaramataWeight_nonneg ht)
      (summable_zetaBinomialHalfKaramataWeight ht),
    tsum_zetaBinomialHalfKaramataWeight ht, ENNReal.ofReal_one]

theorem zetaBinomialHalfKaramataLawRaw_Iio_zero {t : ℝ} (ht : 0 < t) :
    zetaBinomialHalfKaramataLawRaw t (Iio 0) = 0 := by
  exact GaloisForLFunctions.HTGeometry.weightedPointLaw_Iio_zero _ _
    (fun n => mul_nonneg ht.le (Real.log_natCast_nonneg n))

theorem integrable_exp_neg_zetaBinomialHalfKaramataLawRaw
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Integrable (fun y : ℝ => Real.exp (-((k : ℝ) * y)))
      (zetaBinomialHalfKaramataLawRaw t) := by
  letI := isProbabilityMeasure_zetaBinomialHalfKaramataLawRaw ht
  refine Integrable.mono' (integrable_const 1)
    ((Real.measurable_exp.comp
      ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable) ?_
  filter_upwards [GaloisForLFunctions.HTGeometry.ae_nonneg_of_Iio_zero
    (zetaBinomialHalfKaramataLawRaw_Iio_zero ht)] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have hk : 0 ≤ (k : ℝ) := by positivity
  nlinarith

/-- Exact natural Laplace moment of the raw zeta-half Karamata law. -/
theorem integral_exp_neg_zetaBinomialHalfKaramataLawRaw
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (∫ y : ℝ, Real.exp (-((k : ℝ) * y))
        ∂(zetaBinomialHalfKaramataLawRaw t)) =
      zetaBinomialHalfDirichletMass (((k : ℝ) + 1) * t) /
        zetaBinomialHalfDirichletMass t := by
  rw [zetaBinomialHalfKaramataLawRaw,
    GaloisForLFunctions.HTGeometry.integral_weightedPointLaw _ _
      (integrable_exp_neg_zetaBinomialHalfKaramataLawRaw ht k)]
  rw [zetaBinomialHalfDirichletMass, ← tsum_div_const]
  refine tsum_congr fun n => ?_
  rw [ENNReal.toReal_ofReal (zetaBinomialHalfKaramataWeight_nonneg ht n)]
  rw [zetaBinomialHalfKaramataWeight, div_mul_eq_mul_div]
  congr 1
  by_cases hn : n = 0
  · subst n
    simp
  · rw [zetaBinomialHalfKaramataLogCoordinate]
    have hexp : Real.exp (-((k : ℝ) * (t * Real.log n))) =
        (n : ℝ) ^ (-((k : ℝ) * t)) := by
      rw [← GaloisForLFunctions.HTGeometry.exp_neg_mul_log_natCast
        (u := (k : ℝ) * t) hn]
      congr 1
      ring
    rw [hexp]
    rw [mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < n)]
    congr 2
    ring

/-- Real form of the square-root pole limit. -/
theorem tendsto_sqrt_mul_zetaBinomialHalfDirichletMass :
    Tendsto
      (fun t : ℝ => Real.sqrt t * zetaBinomialHalfDirichletMass t)
      (𝓝[>] 0) (𝓝 1) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    tendsto_sqrt_mul_LSeries_zetaBinomialHalf_one_add
  convert h using 1
  · funext t
    rw [zetaBinomialHalfDirichletMass_eq_LSeries_re]
    simp [Complex.mul_re]
  · simp

private theorem tendsto_pos_mul_nhdsGT_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using
      ((tendsto_const_nhds.mul tendsto_id :
        Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0))).mono_left
          nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

/-- Fractional-pole rigidity: every normalized Laplace moment tends to the Gamma-half moment. -/
theorem tendsto_zetaBinomialHalfDirichletMass_ratio (k : ℕ) :
    Tendsto
      (fun t : ℝ =>
        zetaBinomialHalfDirichletMass (((k : ℝ) + 1) * t) /
          zetaBinomialHalfDirichletMass t)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.sqrt ((k : ℝ) + 1))⁻¹)) := by
  let c : ℝ := (k : ℝ) + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let A : ℝ → ℝ := fun t => Real.sqrt t * zetaBinomialHalfDirichletMass t
  have hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    exact tendsto_sqrt_mul_zetaBinomialHalfDirichletMass
  have hAc : Tendsto (fun t : ℝ => A (c * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    hA.comp (tendsto_pos_mul_nhdsGT_zero hc)
  have hquot : Tendsto (fun t : ℝ => A (c * t) / A t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    change Tendsto ((fun t : ℝ => A (c * t)) / A) (𝓝[>] (0 : ℝ)) (𝓝 1)
    simpa only [div_one] using hAc.div hA one_ne_zero
  have hlim := hquot.mul (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (Real.sqrt c)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 ((Real.sqrt c)⁻¹)))
  have hlim' : Tendsto
      (fun t : ℝ => (A (c * t) / A t) * (Real.sqrt c)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Real.sqrt c)⁻¹)) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hMt : zetaBinomialHalfDirichletMass t ≠ 0 :=
    (zetaBinomialHalfDirichletMass_pos ht0).ne'
  have hsqrtt : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have hsqrtc : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  dsimp [A]
  rw [Real.sqrt_mul hc.le]
  field_simp
  congr 1
  dsimp [c]
  ring

/-- Total probability law, with the limiting Gamma-half law used away from `t > 0`. -/
def zetaBinomialHalfKaramataLaw (t : ℝ) : Measure ℝ :=
  if 0 < t then zetaBinomialHalfKaramataLawRaw t else gammaMeasure (1 / 2) 1

instance instIsProbabilityMeasureZetaBinomialHalfKaramataLaw (t : ℝ) :
    IsProbabilityMeasure (zetaBinomialHalfKaramataLaw t) := by
  rw [zetaBinomialHalfKaramataLaw]
  split_ifs with ht
  · exact isProbabilityMeasure_zetaBinomialHalfKaramataLawRaw ht
  · exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)

theorem zetaBinomialHalfKaramataLaw_Iio_zero (t : ℝ) :
    zetaBinomialHalfKaramataLaw t (Iio 0) = 0 := by
  rw [zetaBinomialHalfKaramataLaw]
  split_ifs with ht
  · exact zetaBinomialHalfKaramataLawRaw_Iio_zero ht
  · exact GaloisForLFunctions.HTGeometry.gammaMeasure_half_Iio_zero

theorem tendsto_integral_exp_neg_zetaBinomialHalfKaramataLaw (k : ℕ) :
    Tendsto
      (fun t : ℝ => ∫ y : ℝ, Real.exp (-((k : ℝ) * y))
        ∂(zetaBinomialHalfKaramataLaw t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y : ℝ, Real.exp (-((k : ℝ) * y))
        ∂(gammaMeasure (1 / 2) 1))) := by
  rw [GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_gammaMeasure_half_eq_inv_sqrt
    (k : ℝ) (by positivity)]
  rw [add_comm 1 (k : ℝ)]
  refine (tendsto_zetaBinomialHalfDirichletMass_ratio k).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [zetaBinomialHalfKaramataLaw, if_pos ht]
  exact (integral_exp_neg_zetaBinomialHalfKaramataLawRaw ht k).symm

/-- Exponentially compactified positive zeta-half law. -/
def zetaBinomialHalfKaramataCompactLaw (t : ℝ) :
    ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  GaloisForLFunctions.HTGeometry.expPushProb (zetaBinomialHalfKaramataLaw t)

/-- Exponentially compactified Gamma-half target law. -/
def gammaHalfCompactLaw : ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  letI : IsProbabilityMeasure (gammaMeasure (1 / 2) 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  GaloisForLFunctions.HTGeometry.expPushProb (gammaMeasure (1 / 2) 1)

/-- **Unconditional Karamata law for the positive zeta half.** -/
theorem tendsto_zetaBinomialHalfKaramataCompactLaw :
    Tendsto zetaBinomialHalfKaramataCompactLaw
      (𝓝[>] (0 : ℝ)) (𝓝 gammaHalfCompactLaw) := by
  letI : IsProbabilityMeasure (gammaMeasure (1 / 2) 1) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  apply GaloisForLFunctions.HTGeometry.tendsto_expPushProb_of_tendsto_laplace
  · exact zetaBinomialHalfKaramataLaw_Iio_zero
  · exact GaloisForLFunctions.HTGeometry.gammaMeasure_half_Iio_zero
  · exact tendsto_integral_exp_neg_zetaBinomialHalfKaramataLaw

end RHTower
