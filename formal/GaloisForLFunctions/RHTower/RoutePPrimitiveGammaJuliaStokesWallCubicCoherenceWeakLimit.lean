import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyFloor
import GaloisForLFunctions.HTGeometry.ExponentialCompactification
import GaloisForLFunctions.HTGeometry.ExponentialLaplaceValue

/-!
# P-G105S: SP-E cubic-coherence weak limit

The valuation-one transported-prime wall law, normalized by its exact first-trace current,
converges to the unit exponential law.  Laplace moments give compactified weak convergence and
CDF convergence; quantile coupling then transports the bounded cubic Cauchy coherence across its
single singular corner.  Consequently the normalized two-prime coherence expectation converges
to its independent exponential counterpart.

No Xi-divisor identification or determinant wall passage is asserted here.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

def routePPrimitiveGammaJuliaStokesWallPowerMoment
    (k : ℕ) (d : ℝ) : ℝ :=
  ∑' p : Nat.Primes,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
      routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ k

theorem wallCoordinate_pow_nat
    (d : ℝ) (p : Nat.Primes) (k : ℕ) :
    routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ k =
      (p : ℝ) ^ (-2 * (k : ℝ) * d) := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.pos.le
  rw [routePPrimitiveGammaJuliaStokesWallCoordinate]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hp]
  congr 1
  ring

theorem wallPowerMomentTerm_eq_dilatedWeight
    {d : ℝ} (hd : 0 < d) (k : ℕ) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
        routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ k =
      (1 / ((k : ℝ) + 1)) *
        routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
          (((k : ℝ) + 1) * d) p := by
  have h := wall_weight_mul_rpow_dilation hd
    (show 0 < (k : ℝ) + 1 by positivity) p
  rw [wallCoordinate_pow_nat]
  convert h using 1 <;> ring

theorem summable_wallPowerMoment
    {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
        routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ k) := by
  have hs := summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
    (show 0 < ((k : ℝ) + 1) * d by positivity)
  exact (hs.mul_left (1 / ((k : ℝ) + 1))).congr
    (fun p => (wallPowerMomentTerm_eq_dilatedWeight hd k p).symm)

theorem wallPowerMoment_eq_dilatedCurrent
    {d : ℝ} (hd : 0 < d) (k : ℕ) :
    routePPrimitiveGammaJuliaStokesWallPowerMoment k d =
      (1 / ((k : ℝ) + 1)) *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (((k : ℝ) + 1) * d) := by
  rw [routePPrimitiveGammaJuliaStokesWallPowerMoment]
  calc
    (∑' p : Nat.Primes,
      routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p *
        routePPrimitiveGammaJuliaStokesWallCoordinate d p ^ k) =
        ∑' p : Nat.Primes, (1 / ((k : ℝ) + 1)) *
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
            (((k : ℝ) + 1) * d) p :=
      tsum_congr (wallPowerMomentTerm_eq_dilatedWeight hd k)
    _ = (1 / ((k : ℝ) + 1)) *
        (∑' p : Nat.Primes,
          routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
            (((k : ℝ) + 1) * d) p) := by
      rw [tsum_mul_left]
    _ = _ := by
      rw [tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight
        (show 0 < ((k : ℝ) + 1) * d by positivity)]

private theorem tendsto_pos_mul_nhdsGT_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun d : ℝ => c * d) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · simpa using
      ((tendsto_const_nhds.mul tendsto_id :
        Tendsto (fun d : ℝ => c * d) (𝓝 0) (𝓝 (c * 0))).mono_left
          nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with d hd
    exact mul_pos hc hd

theorem tendsto_wallPowerMoment_nhdsGT_zero (k : ℕ) :
    Tendsto (routePPrimitiveGammaJuliaStokesWallPowerMoment k)
      (𝓝[>] (0 : ℝ)) (𝓝 (4 / ((k : ℝ) + 1))) := by
  have hW : Tendsto
      (fun d : ℝ =>
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (((k : ℝ) + 1) * d))
      (𝓝[>] (0 : ℝ)) (𝓝 4) :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero.comp
      (tendsto_pos_mul_nhdsGT_zero (show 0 < (k : ℝ) + 1 by positivity))
  have hscaled := hW.const_mul (1 / ((k : ℝ) + 1))
  have hscaled' : Tendsto
      (fun d : ℝ => (1 / ((k : ℝ) + 1)) *
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (((k : ℝ) + 1) * d))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 / ((k : ℝ) + 1))) := by
    convert hscaled using 1 <;> ring
  refine hscaled'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (wallPowerMoment_eq_dilatedCurrent hd k).symm

def routePPrimitiveGammaJuliaStokesWallLogCoordinate
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  2 * d * Real.log (p : ℝ)

theorem wallLogCoordinate_pos
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 < routePPrimitiveGammaJuliaStokesWallLogCoordinate d p := by
  rw [routePPrimitiveGammaJuliaStokesWallLogCoordinate]
  exact mul_pos (mul_pos (by norm_num) hd)
    (Real.log_pos (by exact_mod_cast p.property.one_lt))

def routePPrimitiveGammaJuliaStokesWallNormalizedWeight
    (d : ℝ) (p : Nat.Primes) : ℝ :=
  routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d

theorem wallNormalizedWeight_nonneg
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p := by
  exact div_nonneg
    (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd p)
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).le

theorem summable_wallNormalizedWeight
    {d : ℝ} (hd : 0 < d) :
    Summable (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d) := by
  change Summable (fun p : Nat.Primes =>
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p /
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
  exact
    (summable_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd).div_const
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)

theorem tsum_wallNormalizedWeight
    {d : ℝ} (hd : 0 < d) :
    ∑' p : Nat.Primes,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p = 1 := by
  simp only [routePPrimitiveGammaJuliaStokesWallNormalizedWeight]
  rw [tsum_div_const,
    tsum_routePPrimitiveGammaJuliaStokesTransportedPrimeWeight hd]
  exact div_self
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'

def routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw (d : ℝ) : Measure ℝ :=
  GaloisForLFunctions.HTGeometry.weightedPointLaw
    (routePPrimitiveGammaJuliaStokesWallLogCoordinate d)
    (fun p : Nat.Primes =>
      ENNReal.ofReal
        (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p))

theorem isProbabilityMeasure_wallHalfLineLawRaw
    {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
  refine GaloisForLFunctions.HTGeometry.isProbabilityMeasure_weightedPointLaw _ _ ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (wallNormalizedWeight_nonneg hd)
      (summable_wallNormalizedWeight hd),
    tsum_wallNormalizedWeight hd, ENNReal.ofReal_one]

theorem wallHalfLineLawRaw_Iio_zero
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d (Iio 0) = 0 := by
  exact GaloisForLFunctions.HTGeometry.weightedPointLaw_Iio_zero _ _
    (fun p => (wallLogCoordinate_pos hd p).le)

def routePPrimitiveGammaJuliaStokesWallHalfLineLaw (d : ℝ) : Measure ℝ :=
  if 0 < d then routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d
  else expMeasure 1

instance instIsProbabilityMeasureRoutePPrimitiveGammaJuliaStokesWallHalfLineLaw
    (d : ℝ) :
    IsProbabilityMeasure
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) := by
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw]
  split_ifs with hd
  · exact isProbabilityMeasure_wallHalfLineLawRaw hd
  · exact isProbabilityMeasure_expMeasure one_pos

theorem wallHalfLineLaw_Iio_zero (d : ℝ) :
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw d (Iio 0) = 0 := by
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw]
  split_ifs with hd
  · exact wallHalfLineLawRaw_Iio_zero hd
  · exact GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero

theorem wallCoordinate_eq_exp_neg_logCoordinate
    (d : ℝ) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallCoordinate d p =
      Real.exp (-routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) := by
  rw [wallCoordinate_eq_exp,
    routePPrimitiveGammaJuliaStokesWallLogCoordinate]

theorem integrable_exp_neg_wallHalfLineLawRaw
    {d : ℝ} (hd : 0 < d) (k : ℕ) :
    Integrable (fun y : ℝ => Real.exp (-((k : ℝ) * y)))
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
  letI := isProbabilityMeasure_wallHalfLineLawRaw hd
  refine Integrable.mono' (integrable_const 1)
    ((Real.measurable_exp.comp
      ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable) ?_
  filter_upwards [GaloisForLFunctions.HTGeometry.ae_nonneg_of_Iio_zero
    (wallHalfLineLawRaw_Iio_zero hd)] with y hy
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  have hk : 0 ≤ (k : ℝ) := by positivity
  nlinarith

theorem integral_exp_neg_wallHalfLineLawRaw
    {d : ℝ} (hd : 0 < d) (k : ℕ) :
    (∫ y : ℝ, Real.exp (-((k : ℝ) * y))
        ∂(routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)) =
      routePPrimitiveGammaJuliaStokesWallPowerMoment k d /
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d := by
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw,
    GaloisForLFunctions.HTGeometry.integral_weightedPointLaw _ _
      (integrable_exp_neg_wallHalfLineLawRaw hd k)]
  rw [routePPrimitiveGammaJuliaStokesWallPowerMoment]
  rw [← tsum_div_const]
  refine tsum_congr fun p => ?_
  rw [ENNReal.toReal_ofReal (wallNormalizedWeight_nonneg hd p),
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight,
    div_mul_eq_mul_div, wallCoordinate_eq_exp_neg_logCoordinate,
    ← Real.exp_nat_mul]
  congr 2
  ring

theorem tendsto_wallPowerMoment_div_current_nhdsGT_zero (k : ℕ) :
    Tendsto
      (fun d : ℝ =>
        routePPrimitiveGammaJuliaStokesWallPowerMoment k d /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / ((k : ℝ) + 1))) := by
  have hM : Tendsto
      (fun d : ℝ => routePPrimitiveGammaJuliaStokesWallPowerMoment k d)
      (𝓝[>] (0 : ℝ)) (𝓝 (4 / ((k : ℝ) + 1))) :=
    tendsto_wallPowerMoment_nhdsGT_zero k
  have hW : Tendsto
      (fun d : ℝ => gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
      (𝓝[>] (0 : ℝ)) (𝓝 4) :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have h := hM.div hW (by norm_num : (4 : ℝ) ≠ 0)
  have h' : Tendsto
      (fun d : ℝ =>
        routePPrimitiveGammaJuliaStokesWallPowerMoment k d /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / ((k : ℝ) + 1)) / 4)) := by
    exact h
  have hval : (4 / ((k : ℝ) + 1)) / 4 =
      1 / ((k : ℝ) + 1) := by ring
  rwa [hval] at h'

theorem tendsto_integral_exp_neg_wallHalfLineLaw_nhdsGT_zero (k : ℕ) :
    Tendsto
      (fun d : ℝ => ∫ y : ℝ, Real.exp (-((k : ℝ) * y))
        ∂(routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (1 + (k : ℝ)))) := by
  have h := tendsto_wallPowerMoment_div_current_nhdsGT_zero k
  have h' : Tendsto
      (fun d : ℝ =>
        routePPrimitiveGammaJuliaStokesWallPowerMoment k d /
          gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / (1 + (k : ℝ)))) := by
    convert h using 1 <;> ring
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  change 0 < d at hd
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd]
  exact (integral_exp_neg_wallHalfLineLawRaw hd k).symm

def routePPrimitiveGammaJuliaStokesWallCompactLaw (d : ℝ) :
    ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  GaloisForLFunctions.HTGeometry.expPushProb
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)

def routePPrimitiveGammaJuliaStokesWallUniformLaw :
    ProbabilityMeasure (Icc (0 : ℝ) 1) :=
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure one_pos
  GaloisForLFunctions.HTGeometry.expPushProb (expMeasure 1)

theorem tendsto_wallCompactLaw_nhdsGT_zero :
    Tendsto routePPrimitiveGammaJuliaStokesWallCompactLaw
      (𝓝[>] (0 : ℝ))
      (𝓝 routePPrimitiveGammaJuliaStokesWallUniformLaw) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure one_pos
  apply GaloisForLFunctions.HTGeometry.tendsto_expPushProb_of_tendsto_laplace
  · exact wallHalfLineLaw_Iio_zero
  · exact GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero
  · intro k
    rw [GaloisForLFunctions.HTGeometry.integral_exp_neg_expMeasure_one
      (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    exact tendsto_integral_exp_neg_wallHalfLineLaw_nhdsGT_zero k

theorem tendsto_wallHalfLineCDF_nhdsGT_zero (t : ℝ) :
    Tendsto
      (fun d : ℝ => cdf (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) t)
      (𝓝[>] (0 : ℝ)) (𝓝 (cdf (expMeasure 1) t)) := by
  apply GaloisForLFunctions.HTGeometry.tendsto_cdf_expMeasure_one_of_tendsto_laplace
  · exact wallHalfLineLaw_Iio_zero
  · intro k
    rw [GaloisForLFunctions.HTGeometry.integral_exp_neg_expMeasure_one
      (by positivity : (0 : ℝ) ≤ (k : ℝ))]
    exact tendsto_integral_exp_neg_wallHalfLineLaw_nhdsGT_zero k

theorem tendsto_wallHalfLineQuantile_nhdsGT_zero
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    Tendsto
      (fun d : ℝ => GaloisForLFunctions.HTGeometry.quantile
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (GaloisForLFunctions.HTGeometry.quantile (expMeasure 1) u)) := by
  exact GaloisForLFunctions.HTGeometry.tendsto_quantile_expMeasure_one
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw
    tendsto_wallHalfLineCDF_nhdsGT_zero hu0 hu1

def routePPrimitiveGammaJuliaStokesWallCubicCoherence
    (a b : ℝ) : ℝ :=
  routePBaseCauchyCubicNormalizedCoherenceSq a b 0

theorem wallCubicCoherence_zero_le_one
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallCubicCoherence a b ∧
      routePPrimitiveGammaJuliaStokesWallCubicCoherence a b ≤ 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallCubicCoherence,
    routePBaseCauchyCubicNormalizedCoherenceSq]
  norm_num
  constructor
  · positivity
  · by_cases hab : a + b = 0
    · have ha0 : a = 0 := by nlinarith
      simp [ha0]
    · have hbase : 4 * a * b ≤ (a + b) ^ 2 := by
        nlinarith [sq_nonneg (a - b)]
      have hbase0 : 0 ≤ 4 * a * b := by positivity
      have hcubes := pow_le_pow_left₀ hbase0 hbase 3
      rw [show (4 * a * b) ^ 3 = 64 * a ^ 3 * b ^ 3 by ring] at hcubes
      rw [div_le_one (pow_pos (sq_pos_of_ne_zero hab) 3)]
      simpa only [pow_mul] using hcubes

theorem measurable_wallCubicCoherence :
    Measurable (fun z : ℝ × ℝ =>
      routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2) := by
  unfold routePPrimitiveGammaJuliaStokesWallCubicCoherence
    routePBaseCauchyCubicNormalizedCoherenceSq
  fun_prop

theorem tendsto_wallCubicCoherence
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {A B : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hA : 0 < A) (hB : 0 < B) :
    Tendsto
      (fun i => routePPrimitiveGammaJuliaStokesWallCubicCoherence (a i) (b i))
      l (𝓝 (routePPrimitiveGammaJuliaStokesWallCubicCoherence A B)) := by
  unfold routePPrimitiveGammaJuliaStokesWallCubicCoherence
    routePBaseCauchyCubicNormalizedCoherenceSq
  norm_num
  apply Tendsto.div
  · exact (tendsto_const_nhds.mul (ha.pow 3)).mul (hb.pow 3)
  · exact ((ha.add hb).pow 2).pow 3
  · positivity

def routePPrimitiveGammaJuliaStokesWallQuantileCoherence
    (μ : Measure ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2 ∈ Ioo (0 : ℝ) 1 then
    routePPrimitiveGammaJuliaStokesWallCubicCoherence
      (GaloisForLFunctions.HTGeometry.quantile μ z.1)
      (GaloisForLFunctions.HTGeometry.quantile μ z.2)
  else 0

theorem measurable_wallQuantileCoherence
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (routePPrimitiveGammaJuliaStokesWallQuantileCoherence μ) := by
  unfold routePPrimitiveGammaJuliaStokesWallQuantileCoherence
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_Ioo.preimage measurable_fst).inter
      (measurableSet_Ioo.preimage measurable_snd)
  · let q : ℝ → ℝ := GaloisForLFunctions.HTGeometry.quantile μ
    have hq : Measurable q := GaloisForLFunctions.HTGeometry.measurable_quantile μ
    have hq1 : Measurable (fun z : ℝ × ℝ => q z.1) := hq.comp measurable_fst
    have hq2 : Measurable (fun z : ℝ × ℝ => q z.2) := hq.comp measurable_snd
    unfold routePPrimitiveGammaJuliaStokesWallCubicCoherence
      routePBaseCauchyCubicNormalizedCoherenceSq
    exact ((measurable_const.mul (hq1.pow_const 3)).mul (hq2.pow_const 3)).div
      ((((hq1.add hq2).pow_const 2).add (measurable_const.pow_const 2)).pow_const 3)

theorem wallQuantileCoherence_norm_le_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0) (z : ℝ × ℝ) :
    ‖routePPrimitiveGammaJuliaStokesWallQuantileCoherence μ z‖ ≤ 1 := by
  unfold routePPrimitiveGammaJuliaStokesWallQuantileCoherence
  split_ifs with hz
  · have ha := GaloisForLFunctions.HTGeometry.quantile_nonneg hsupp hz.1.1 hz.1.2
    have hb := GaloisForLFunctions.HTGeometry.quantile_nonneg hsupp hz.2.1 hz.2.2
    have h := wallCubicCoherence_zero_le_one ha hb
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  · norm_num

theorem tendsto_wallQuantileCoherence_nhdsGT_zero (z : ℝ × ℝ) :
    Tendsto
      (fun d : ℝ => routePPrimitiveGammaJuliaStokesWallQuantileCoherence
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePPrimitiveGammaJuliaStokesWallQuantileCoherence (expMeasure 1) z)) := by
  unfold routePPrimitiveGammaJuliaStokesWallQuantileCoherence
  split_ifs with hz
  · apply tendsto_wallCubicCoherence
    · exact tendsto_wallHalfLineQuantile_nhdsGT_zero hz.1.1 hz.1.2
    · exact tendsto_wallHalfLineQuantile_nhdsGT_zero hz.2.1 hz.2.2
    · rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hz.1.1 hz.1.2]
      exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hz.1.2) (by linarith [hz.1.1]))
    · rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hz.2.1 hz.2.2]
      exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hz.2.2) (by linarith [hz.2.1]))
  · exact tendsto_const_nhds

def routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0 : ℝ) 1)).prod
    (volume.restrict (Ioo (0 : ℝ) 1))

instance instIsFiniteMeasureRoutePPrimitiveGammaJuliaStokesWallUnitSquareMeasure :
    IsFiniteMeasure routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure := by
  rw [routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure]
  infer_instance

theorem tendsto_integral_wallQuantileCoherence_nhdsGT_zero :
    Tendsto
      (fun d : ℝ => ∫ z : ℝ × ℝ,
        routePPrimitiveGammaJuliaStokesWallQuantileCoherence
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z : ℝ × ℝ,
        routePPrimitiveGammaJuliaStokesWallQuantileCoherence (expMeasure 1) z
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure)) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun d =>
      (measurable_wallQuantileCoherence
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun d =>
      Filter.Eventually.of_forall fun z =>
        wallQuantileCoherence_norm_le_one
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
          (wallHalfLineLaw_Iio_zero d) z
  · exact integrable_const 1
  · exact Filter.Eventually.of_forall tendsto_wallQuantileCoherence_nhdsGT_zero

theorem ae_mem_wallUnitSquare :
    ∀ᵐ z : ℝ × ℝ ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure,
      z.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2 ∈ Ioo (0 : ℝ) 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure]
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact ⟨hx, hy⟩

theorem integral_wallQuantileCoherence_eq_prod
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ z : ℝ × ℝ,
      routePPrimitiveGammaJuliaStokesWallQuantileCoherence μ z
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure) =
      ∫ z : ℝ × ℝ,
        routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
        ∂(μ.prod μ) := by
  let m : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let q : ℝ → ℝ := GaloisForLFunctions.HTGeometry.quantile μ
  have hq : Measurable q := GaloisForLFunctions.HTGeometry.measurable_quantile μ
  have hpair : Measurable (Prod.map q q) := hq.prodMap hq
  have hpiece :
      (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallQuantileCoherence μ z
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure) =
      ∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (q z.1) (q z.2) ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_mem_wallUnitSquare] with z hz
    simp [routePPrimitiveGammaJuliaStokesWallQuantileCoherence, hz, q]
  have hmap : μ.prod μ = Measure.map (Prod.map q q) (m.prod m) := by
    have hp := Measure.map_prod_map m m hq hq
    dsimp [m, q] at hp ⊢
    rw [GaloisForLFunctions.HTGeometry.map_quantile_eq μ] at hp
    exact hp
  rw [hpiece, hmap]
  have hi := integral_map hpair.aemeasurable
    measurable_wallCubicCoherence.aestronglyMeasurable
    (μ := m.prod m)
  rw [routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure]
  exact hi.symm

theorem tendsto_integral_wallCubicCoherence_prod_nhdsGT_zero :
    Tendsto
      (fun d : ℝ => ∫ z : ℝ × ℝ,
        routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
        ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z : ℝ × ℝ,
        routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
        ∂((expMeasure 1).prod (expMeasure 1)))) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  rw [← integral_wallQuantileCoherence_eq_prod (expMeasure 1)]
  refine tendsto_integral_wallQuantileCoherence_nhdsGT_zero.congr' ?_
  filter_upwards with d
  exact integral_wallQuantileCoherence_eq_prod
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)

end

end RHTower

