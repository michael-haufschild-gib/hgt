import GaloisForLFunctions.RHTower.SuzukiCanonicalKernelContinuity
import GaloisForLFunctions.RHTower.SuzukiCanonicalArithmeticMellin
import GaloisForLFunctions.HTGeometry.EndpointIntegralAsymptotics

/-!
# Real form of Suzuki's compact archimedean kernel

On its support `0 < x < 1` Suzuki's kernel

`g_ω(x) = (2π^ω/Γ(ω)) ( x^{2-ω}(1-x²)^{ω-1} - ω x^{ω-1} T_ω(x) )`,
`T_ω(x) = ∫_{x²}^1 t^{1/2-ω}(1-t)^{ω-1} dt`,

takes only real values, and so does its once-integrated primitive
`g_ω^{⟨1⟩}(x) = ∫_x^1 √(y/x) g_ω(y) dy/y`.  This module introduces the real-valued versions,
identifies them with the complex source kernels, and records the analytic facts about the
incomplete-beta tail that the endpoint expansions need:

* the complete beta value `T_ω(0) = Γ(3/2-ω)Γ(ω)/Γ(3/2)` for `0 < ω < 3/2`;
* continuity of `T_ω` up to the endpoint `x = 0`;
* the exact vanishing rate `T_ω(x) ∼ (1-x²)^ω/ω` at `x = 1`;
* interval integrability of the weighted kernel `y^{-1/2} g_ω(y)` on `[x,1]`, `0 < x < 1`, and the
  primitive formula `g_ω^{⟨1⟩}(x) = x^{-1/2} ∫_x^1 y^{-1/2} g_ω(y) dy`.
-/

namespace RHTower

noncomputable section

open Complex MeasureTheory Set Filter Topology

/-! ## The real beta integrand -/

/-- The real incomplete-beta integrand `t^{1/2-ω}(1-t)^{ω-1}`. -/
def suzukiRealBetaIntegrand (ω t : ℝ) : ℝ := t ^ (1 / 2 - ω) * (1 - t) ^ (ω - 1)

theorem ofReal_suzukiRealBetaIntegrand {ω t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((suzukiRealBetaIntegrand ω t : ℝ) : ℂ)
      = (t : ℂ) ^ ((1 / 2 - ω : ℝ) : ℂ) * (1 - (t : ℂ)) ^ ((ω : ℂ) - 1) := by
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  rw [suzukiRealBetaIntegrand, Complex.ofReal_mul, Complex.ofReal_cpow ht0,
    Complex.ofReal_cpow ht1']
  push_cast
  ring

theorem suzukiRealBetaIntegrand_nonneg {ω t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ suzukiRealBetaIntegrand ω t := by
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  exact mul_nonneg (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg ht1' _)

/-- Interval integrability of the real beta integrand on the whole unit interval. -/
theorem intervalIntegrable_suzukiRealBetaIntegrand {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    IntervalIntegrable (suzukiRealBetaIntegrand ω) volume 0 1 := by
  have hu : (0 : ℝ) < (((3 / 2 - ω : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hv : (0 : ℝ) < (((ω : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hC := Complex.betaIntegral_convergent hu hv
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hC ⊢
  have he1 : ((3 / 2 - ω : ℝ) : ℂ) - 1 = ((1 / 2 - ω : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he1] at hC
  have hcongr : IntegrableOn (fun t : ℝ => ((suzukiRealBetaIntegrand ω t : ℝ) : ℂ))
      (Ioc 0 1) := by
    refine hC.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [ofReal_suzukiRealBetaIntegrand ht.1.le ht.2]
  exact hcongr.re

/-! ## The real beta tail -/

/-- The real incomplete-beta tail `T_ω(x) = ∫_{x²}^1 t^{1/2-ω}(1-t)^{ω-1} dt`. -/
def suzukiRealBetaTail (ω x : ℝ) : ℝ := ∫ t in Ioc (x ^ 2) 1, suzukiRealBetaIntegrand ω t

theorem ofReal_suzukiRealBetaTail (ω x : ℝ) :
    ((suzukiRealBetaTail ω x : ℝ) : ℂ) = suzukiBetaTail ω x := by
  rw [suzukiRealBetaTail, suzukiBetaTail, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans (by positivity) ht.1.le
  exact ofReal_suzukiRealBetaIntegrand ht0 ht.2

theorem suzukiRealBetaTail_nonneg (ω : ℝ) (x : ℝ) : 0 ≤ suzukiRealBetaTail ω x := by
  rw [suzukiRealBetaTail]
  refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_trans (by positivity) ht.1.le
  exact suzukiRealBetaIntegrand_nonneg ht0 ht.2

/-- The beta tail as an interval integral. -/
theorem suzukiRealBetaTail_eq_intervalIntegral (ω : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    suzukiRealBetaTail ω x = ∫ t in (x ^ 2)..1, suzukiRealBetaIntegrand ω t := by
  have hsq : x ^ 2 ≤ 1 := by nlinarith
  rw [suzukiRealBetaTail, intervalIntegral.integral_of_le hsq]

/-- **The complete beta value.**  For `0 < ω < 3/2` the tail at the origin is the Euler beta
value `Γ(3/2-ω)Γ(ω)/Γ(3/2)`. -/
theorem suzukiRealBetaTail_zero {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    suzukiRealBetaTail ω 0
      = Real.Gamma (3 / 2 - ω) * Real.Gamma ω / Real.Gamma (3 / 2) := by
  have hu : (0 : ℝ) < (((3 / 2 - ω : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hv : (0 : ℝ) < (((ω : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have hsum : ((3 / 2 - ω : ℝ) : ℂ) + ((ω : ℝ) : ℂ) = ((3 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsum] at hbeta
  have hGamma32 : Real.Gamma (3 / 2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have hint : Complex.betaIntegral ((3 / 2 - ω : ℝ) : ℂ) ((ω : ℝ) : ℂ)
      = ((suzukiRealBetaTail ω 0 : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ofReal_suzukiRealBetaTail ω 0, suzukiBetaTail]
    rw [show (0 : ℝ) ^ 2 = (0 : ℝ) by norm_num,
      ← intervalIntegral.integral_of_le zero_le_one]
    have he1 : ((3 / 2 - ω : ℝ) : ℂ) - 1 = ((1 / 2 - ω : ℝ) : ℂ) := by
      push_cast
      ring
    have he2 : ((ω : ℝ) : ℂ) - 1 = (ω : ℂ) - 1 := rfl
    rw [he1, he2]
  rw [hint] at hbeta
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hbeta
  have hreal : Real.Gamma (3 / 2 - ω) * Real.Gamma ω
      = Real.Gamma (3 / 2) * suzukiRealBetaTail ω 0 := by
    exact_mod_cast hbeta
  rw [eq_div_iff hGamma32]
  linarith [hreal]

/-- Continuity of the beta tail up to the origin. -/
theorem continuousOn_suzukiRealBetaTail {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    ContinuousOn (suzukiRealBetaTail ω) (Icc 0 1) := by
  have hint : IntegrableOn (suzukiRealBetaIntegrand ω) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegrable_suzukiRealBetaIntegrand hω hω')
  have hprim : ContinuousOn (fun u : ℝ => ∫ t in u..1, suzukiRealBetaIntegrand ω t)
      (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval_left hint
    rwa [uIcc_of_le zero_le_one] at this
  have hsq : MapsTo (fun x : ℝ => x ^ 2) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro x hx
    constructor
    · positivity
    · nlinarith [hx.1, hx.2]
  have hcomp : ContinuousOn (fun x : ℝ => ∫ t in (x ^ 2)..1, suzukiRealBetaIntegrand ω t)
      (Icc 0 1) := hprim.comp (continuous_pow 2).continuousOn hsq
  refine hcomp.congr fun x hx => ?_
  exact suzukiRealBetaTail_eq_intervalIntegral ω hx.1 hx.2

/-- The beta tail converges to the complete beta value at the origin. -/
theorem tendsto_suzukiRealBetaTail_nhdsGT_zero {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (suzukiRealBetaTail ω) (𝓝[>] (0 : ℝ)) (𝓝 (suzukiRealBetaTail ω 0)) := by
  have hcont := continuousOn_suzukiRealBetaTail hω hω'
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  refine (hcont 0 h0).mono_left (nhdsWithin_le_iff.2 ?_)
  exact mem_of_superset (Ioo_mem_nhdsGT one_pos) Ioo_subset_Icc_self

/-! ## The real kernel -/

/-- Real form of Suzuki's compact kernel `g_ω`. -/
def suzukiRealSourceG (ω x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    (2 * Real.pi ^ ω / Real.Gamma ω) *
      (x ^ (2 - ω) * (1 - x ^ 2) ^ (ω - 1) - ω * x ^ (ω - 1) * suzukiRealBetaTail ω x)
  else 0

theorem ofReal_suzukiRealSourceG (ω x : ℝ) :
    ((suzukiRealSourceG ω x : ℝ) : ℂ) = suzukiSourceG ω x := by
  by_cases hx : 0 < x ∧ x < 1
  · have hx0 : (0 : ℝ) ≤ x := hx.1.le
    have hsq : (0 : ℝ) ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
    rw [suzukiRealSourceG, if_pos hx, suzukiSourceG, if_pos hx,
      ← ofReal_suzukiRealBetaTail ω x]
    rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_cpow hx0 (2 - ω), Complex.ofReal_cpow hsq (ω - 1),
      Complex.ofReal_cpow hx0 (ω - 1), Complex.ofReal_cpow Real.pi_pos.le ω,
      ← Complex.Gamma_ofReal]
    push_cast
    ring
  · rw [suzukiRealSourceG, if_neg hx, suzukiSourceG, if_neg hx, Complex.ofReal_zero]

theorem suzukiRealSourceG_eq_zero_of_one_le {ω x : ℝ} (hx : 1 ≤ x) :
    suzukiRealSourceG ω x = 0 := by
  rw [suzukiRealSourceG, if_neg]
  exact fun h => absurd h.2 (not_lt.2 hx)

theorem suzukiRealSourceG_eq_zero_of_nonpos {ω x : ℝ} (hx : x ≤ 0) :
    suzukiRealSourceG ω x = 0 := by
  rw [suzukiRealSourceG, if_neg]
  exact fun h => absurd h.1 (not_lt.2 hx)

/-- The explicit interior formula, valid at every interior point of the support. -/
theorem suzukiRealSourceG_apply {ω x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    suzukiRealSourceG ω x
      = (2 * Real.pi ^ ω / Real.Gamma ω) *
        (x ^ (2 - ω) * (1 - x ^ 2) ^ (ω - 1) - ω * x ^ (ω - 1) * suzukiRealBetaTail ω x) := by
  rw [suzukiRealSourceG, if_pos ⟨hx0, hx1⟩]

/-! ## The weighted kernel and the primitive -/

/-- The weighted kernel `y^{-1/2} g_ω(y)` entering Suzuki's primitive. -/
def suzukiRealSourceGWeighted (ω y : ℝ) : ℝ := y ^ (-(1 / 2) : ℝ) * suzukiRealSourceG ω y

/-- Real form of Suzuki's once-integrated kernel. -/
def suzukiRealSourceGOne (ω x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    ∫ y in Ioc x 1, Real.sqrt (y / x) * suzukiRealSourceG ω y / y
  else 0

theorem ofReal_suzukiRealSourceGOne (ω x : ℝ) :
    ((suzukiRealSourceGOne ω x : ℝ) : ℂ) = suzukiSourceGOne ω x := by
  by_cases hx : 0 < x ∧ x < 1
  · rw [suzukiRealSourceGOne, if_pos hx, suzukiSourceGOne, if_pos hx,
      ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with y
    rw [Complex.ofReal_div, Complex.ofReal_mul, ofReal_suzukiRealSourceG]
  · rw [suzukiRealSourceGOne, if_neg hx, suzukiSourceGOne, if_neg hx, Complex.ofReal_zero]

theorem suzukiRealSourceGOne_eq_zero_of_one_le {ω x : ℝ} (hx : 1 ≤ x) :
    suzukiRealSourceGOne ω x = 0 := by
  rw [suzukiRealSourceGOne, if_neg]
  exact fun h => absurd h.2 (not_lt.2 hx)

/-- The primitive in weighted form. -/
theorem suzukiRealSourceGOne_eq_weighted {ω x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    suzukiRealSourceGOne ω x
      = x ^ (-(1 / 2) : ℝ) * ∫ y in x..1, suzukiRealSourceGWeighted ω y := by
  rw [suzukiRealSourceGOne, if_pos ⟨hx0, hx1⟩,
    ← intervalIntegral.integral_of_le hx1.le, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hx1.le] at hy
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hy.1
  show Real.sqrt (y / x) * suzukiRealSourceG ω y / y
      = x ^ (-(1 / 2) : ℝ) * suzukiRealSourceGWeighted ω y
  have hxs : Real.sqrt (y / x) = y ^ (1 / 2 : ℝ) * x ^ (-(1 / 2) : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow hy0.le hx0.le, Real.rpow_neg hx0.le, div_eq_mul_inv]
  have hy2 : y ^ (1 / 2 : ℝ) / y = y ^ (-(1 / 2) : ℝ) := by
    rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by ring, Real.rpow_sub hy0, Real.rpow_one]
  rw [suzukiRealSourceGWeighted, hxs, ← hy2]
  ring

/-! ## The vanishing rate of the beta tail at the endpoint -/

/-- Interval integrability of the beta integrand on every subinterval of the unit interval. -/
theorem intervalIntegrable_suzukiRealBetaIntegrand_sub {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    IntervalIntegrable (suzukiRealBetaIntegrand ω) volume u 1 :=
  (intervalIntegrable_suzukiRealBetaIntegrand hω hω').mono_set (by
    rw [uIcc_of_le hu1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hu0 le_rfl)

/-- **The exact vanishing rate of the beta tail.**  `∫_u^1 t^{1/2-ω}(1-t)^{ω-1} dt ∼ (1-u)^ω/ω`
as `u → 1⁻`. -/
theorem tendsto_betaIntegrandPrimitive_nhdsLT_one {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (fun u : ℝ => (1 - u) ^ (-ω) * ∫ t in u..1, suzukiRealBetaIntegrand ω t)
      (𝓝[<] (1 : ℝ)) (𝓝 (1 / ω)) := by
  have hβ : (-1 : ℝ) < ω - 1 := by linarith
  have hint : ∀ u ∈ Ioo (0 : ℝ) 1, IntervalIntegrable (suzukiRealBetaIntegrand ω) volume u 1 :=
    fun u hu => intervalIntegrable_suzukiRealBetaIntegrand_sub hω hω' hu.1.le hu.2.le
  have hlim : Tendsto (fun t : ℝ => suzukiRealBetaIntegrand ω t / (1 - t) ^ (ω - 1))
      (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hcont : Tendsto (fun t : ℝ => t ^ (1 / 2 - ω)) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
      have hc : ContinuousAt (fun t : ℝ => t ^ (1 / 2 - ω)) 1 :=
        Real.continuousAt_rpow_const 1 _ (Or.inl one_ne_zero)
      have h1 : (1 : ℝ) ^ (1 / 2 - ω) = 1 := Real.one_rpow _
      have h2 := hc.tendsto
      rw [h1] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht1 : (0 : ℝ) < 1 - t := by
      have : t < 1 := ht
      linarith
    have hne : (1 - t) ^ (ω - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht1 _)
    rw [suzukiRealBetaIntegrand]
    field_simp
  have hmain := HTGeometry.tendsto_rpow_mul_intervalIntegral_nhdsLT hβ zero_lt_one hint hlim
  have hexp : -(ω - 1 + 1) = -ω := by ring
  rw [hexp] at hmain
  have hval : (1 : ℝ) / (ω - 1 + 1) = 1 / ω := by
    congr 1
    ring
  rw [hval] at hmain
  exact hmain

/-- The beta tail vanishes at the rate `(1-y²)^ω/ω` at the endpoint. -/
theorem tendsto_suzukiRealBetaTail_nhdsLT_one {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2) :
    Tendsto (fun y : ℝ => (1 - y ^ 2) ^ (-ω) * suzukiRealBetaTail ω y)
      (𝓝[<] (1 : ℝ)) (𝓝 (1 / ω)) := by
  have hsq : Tendsto (fun y : ℝ => y ^ 2) (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) := by
    have hcont : Tendsto (fun y : ℝ => y ^ 2) (𝓝 (1 : ℝ)) (𝓝 1) := by
      have := (continuous_pow 2 (M := ℝ)).tendsto (1 : ℝ)
      simpa using this
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) one_pos] with y hy
    have hy0 : 0 < y := hy.1
    have hy1 : y < 1 := hy.2
    exact mem_Iio.2 (by nlinarith)
  have hcomp := (tendsto_betaIntegrandPrimitive_nhdsLT_one hω hω').comp hsq
  refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (a := (0 : ℝ)) one_pos] with y hy
  have hy0 : 0 < y := hy.1
  have hy1 : y < 1 := hy.2
  simp only [Function.comp_apply]
  rw [suzukiRealBetaTail_eq_intervalIntegral ω hy0.le hy1.le]

/-! ## The weighted kernel -/

/-- The interior formula for the weighted kernel `y^{-1/2} g_ω(y)`. -/
def suzukiRealWeightedFormula (ω y : ℝ) : ℝ :=
  (2 * Real.pi ^ ω / Real.Gamma ω) *
    ((1 - y) ^ (ω - 1) * (y ^ (3 / 2 - ω) * (1 + y) ^ (ω - 1))
      - ω * (y ^ (ω - 3 / 2) * suzukiRealBetaTail ω y))

theorem suzukiRealSourceGWeighted_eq_formula {ω y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    suzukiRealSourceGWeighted ω y = suzukiRealWeightedFormula ω y := by
  have hy1' : (0 : ℝ) < 1 - y := by linarith
  have hy1'' : (0 : ℝ) < 1 + y := by linarith
  have hfac : (1 : ℝ) - y ^ 2 = (1 - y) * (1 + y) := by ring
  have hsplit : ((1 : ℝ) - y ^ 2) ^ (ω - 1) = (1 - y) ^ (ω - 1) * (1 + y) ^ (ω - 1) := by
    rw [hfac, Real.mul_rpow hy1'.le hy1''.le]
  have hp1 : y ^ (-(1 / 2) : ℝ) * y ^ (2 - ω) = y ^ (3 / 2 - ω) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  have hp2 : y ^ (-(1 / 2) : ℝ) * y ^ (ω - 1) = y ^ (ω - 3 / 2) := by
    rw [← Real.rpow_add hy0]
    congr 1
    ring
  rw [suzukiRealSourceGWeighted, suzukiRealSourceG_apply hy0 hy1, suzukiRealWeightedFormula,
    hsplit, ← hp1, ← hp2]
  ring

/-- Interval integrability of the weighted kernel up to the support endpoint. -/
theorem intervalIntegrable_suzukiRealSourceGWeighted {ω : ℝ} (hω : 0 < ω) (hω' : ω < 3 / 2)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    IntervalIntegrable (suzukiRealSourceGWeighted ω) volume x 1 := by
  have hβ : (-1 : ℝ) < ω - 1 := by linarith
  have hsub : uIcc x 1 = Icc x 1 := uIcc_of_le hx1.le
  have hcont1 : ContinuousOn (fun y : ℝ => y ^ (3 / 2 - ω) * (1 + y) ^ (ω - 1)) (uIcc x 1) := by
    rw [hsub]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_id.rpow_const fun y hy => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hy.1))
    · have hadd : ContinuousOn (fun y : ℝ => 1 + y) (Icc x 1) :=
        (continuous_const.add continuous_id).continuousOn
      exact hadd.rpow_const fun y hy => Or.inl (by have := hy.1; linarith)
  have hcont2 : ContinuousOn (fun y : ℝ => y ^ (ω - 3 / 2) * suzukiRealBetaTail ω y)
      (uIcc x 1) := by
    rw [hsub]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_id.rpow_const fun y hy => Or.inl (ne_of_gt (lt_of_lt_of_le hx0 hy.1))
    · exact (continuousOn_suzukiRealBetaTail hω hω').mono (fun y hy =>
        ⟨le_trans hx0.le hy.1, hy.2⟩)
  have hP1 : IntervalIntegrable
      (fun y : ℝ => (1 - y) ^ (ω - 1) * (y ^ (3 / 2 - ω) * (1 + y) ^ (ω - 1))) volume x 1 :=
    (HTGeometry.intervalIntegrable_sub_rpow (b := 1) hβ).mul_continuousOn hcont1
  have hP2 : IntervalIntegrable (fun y : ℝ => y ^ (ω - 3 / 2) * suzukiRealBetaTail ω y)
      volume x 1 := hcont2.intervalIntegrable
  have hform : IntervalIntegrable (suzukiRealWeightedFormula ω) volume x 1 := by
    have hbase := (hP1.sub (hP2.const_mul ω)).const_mul (2 * Real.pi ^ ω / Real.Gamma ω)
    exact hbase.congr fun y _ => rfl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx1.le] at hform ⊢
  refine hform.congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne 1)] with y hy hyne
  exact (suzukiRealSourceGWeighted_eq_formula (lt_of_lt_of_le hx0 hy.1.le)
    (lt_of_le_of_ne hy.2 hyne)).symm

end

end RHTower
