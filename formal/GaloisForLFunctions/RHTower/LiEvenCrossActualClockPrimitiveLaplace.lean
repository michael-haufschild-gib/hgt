import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveNegative
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitiveVolterra
import GaloisForLFunctions.RHTower.LiClockThetaExactRatioBand
import GaloisForLFunctions.HTGeometry.LaplaceMomentPositivity
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockMaxGrowthRate

/-!
# The logarithmic Laplace transform of the integrated actual clock

Let `P` be the integrated actual clock, `f(t) = P(t)/t`, `Φ(z) = XiC(-iz)/XiC(0)` the normalized
actual generator, `β < 1/300` the maximal imaginary reciprocal frequency and `γ = 1/300`.  For
every `p > β` the weighted moments `M_n(p) = ∫_0^∞ t^n e^{-pt} f(t) dt` converge absolutely, and

* `P̂(p) = Φ'(1/p)/(p² Φ(1/p))`, from `P + P ⋆ K = tK`, `1 + K̂ = Φ(1/p)`, `(tK)^ = Φ'(1/p)/p²`;
* `M_n' = -M_{n+1}` (dominated differentiation);
* `H(p) = M_0(p) = log Φ(1/p) > 0`, because both sides have derivative `-P̂` and vanish at `∞`;
* `(-1)^n (d/dp)^n log Φ(1/p) = M_n(p)`;
* RH holds iff `(-1)^n (d/dp)^n log Φ(1/p) ≥ 0` for every `n` and every `p > γ`: the forward
  direction is `P ≥ 0` under RH, the converse is Laplace-moment localisation at each `t₀ > 0`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

local notation "P" => liEvenCrossActualClockPrimitive
local notation "β" => liEvenCrossActualClockMaxGrowthRate

/-! ## Absolute convergence of the weighted moments -/

theorem abs_liEvenCrossActualClockPrimitive_div_le {t : ℝ} (ht : 0 < t) :
    |P t / t| ≤ xiShiftAbsoluteMass 0 / 2 * t * Real.exp (β * t) := by
  have h := abs_liEvenCrossActualClockPrimitive_le_max ht.le
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
  calc |P t| ≤ xiShiftAbsoluteMass 0 * t ^ 2 / 2 * Real.exp (β * t) := h
    _ = _ := by ring

theorem continuous_liEvenCrossActualClockPrimitive : Continuous P :=
  contDiff_liEvenCrossActualClockPrimitive.continuous

theorem measurable_liEvenCrossActualClockPrimitive_div : Measurable fun t => P t / t :=
  continuous_liEvenCrossActualClockPrimitive.measurable.div measurable_id

/-- The weighted Laplace moments `M_n(p) = ∫_0^∞ t^n e^{-pt} P(t)/t dt`. -/
def liClockPrimitiveLaplaceMoment (n : ℕ) (p : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(p * t)) * (P t / t)

private theorem moment_bound (n : ℕ) (p : ℝ) {t : ℝ} (ht : 0 < t) :
    |t ^ n * Real.exp (-(p * t)) * (P t / t)| ≤
      xiShiftAbsoluteMass 0 / 2 * (t ^ (n + 1) * Real.exp (-((p - β) * t))) := by
  rw [abs_mul, abs_mul, abs_of_pos (pow_pos ht n), abs_of_pos (Real.exp_pos _)]
  calc t ^ n * Real.exp (-(p * t)) * |P t / t| ≤
      t ^ n * Real.exp (-(p * t)) * (xiShiftAbsoluteMass 0 / 2 * t * Real.exp (β * t)) :=
        mul_le_mul_of_nonneg_left (abs_liEvenCrossActualClockPrimitive_div_le ht) (by positivity)
    _ = _ := by
      rw [show -((p - β) * t) = -(p * t) + β * t by ring, Real.exp_add]; ring

private theorem measurable_moment_integrand (n : ℕ) (p : ℝ) :
    Measurable fun t => t ^ n * Real.exp (-(p * t)) * (P t / t) :=
  (by fun_prop : Continuous fun t : ℝ => t ^ n * Real.exp (-(p * t))).measurable.mul
    measurable_liEvenCrossActualClockPrimitive_div

theorem integrableOn_liClockPrimitiveLaplaceMoment (n : ℕ) {p : ℝ} (hp : β < p) :
    IntegrableOn (fun t => t ^ n * Real.exp (-(p * t)) * (P t / t)) (Ioi 0) := by
  have hb : IntegrableOn (fun t => xiShiftAbsoluteMass 0 / 2 * ((n + 1).factorial : ℝ) *
      (dividedPowerFn (n + 1) t * Real.exp (-((p - β) * t)))) (Ioi 0) :=
    (integrableOn_dividedPowerFn_mul_exp_neg (n + 1) (by linarith)).const_mul _
  refine hb.mono' (measurable_moment_integrand n p).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  rw [Real.norm_eq_abs]
  refine (moment_bound n p ht).trans (le_of_eq ?_)
  have hf : ((n + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  unfold dividedPowerFn
  field_simp

theorem integrableOn_exp_mul_abs_liEvenCrossActualClockPrimitive {p : ℝ} (hp : β < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * |P t|) (Ioi 0) := by
  refine IntegrableOn.congr_fun (integrableOn_liClockPrimitiveLaplaceMoment 1 hp).abs
    (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from ht).ne'
  rw [abs_mul, abs_mul, pow_one, abs_div, abs_of_pos (show (0 : ℝ) < t from ht),
    abs_of_pos (Real.exp_pos _)]
  field_simp

theorem integrableOn_exp_mul_liEvenCrossActualClockPrimitive {p : ℝ} (hp : β < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * P t) (Ioi 0) := by
  refine (integrableOn_liClockPrimitiveLaplaceMoment 1 hp).congr_fun (fun t ht => ?_)
    measurableSet_Ioi
  have ht0 : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from ht).ne'
  field_simp

/-! ## The Laplace transform of the integrated clock -/

private theorem abs_two_mul_coeff_le {R : ℝ} (hR : 0 < R) (k : ℕ) :
    |2 * (k : ℝ) * liClockThetaGeneratorCoeff k| ≤
      Real.exp (32 / (303 * R ^ 2)) * (2 * R) ^ (2 * k) := by
  have hc := liClockThetaGeneratorCoeff_le_pow hR k
  have hcpos := liClockThetaGeneratorCoeff_pos k
  have h4 : 2 * (k : ℝ) ≤ 4 ^ k := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 3 by norm_num) k
    norm_num at this
    linarith
  rw [abs_of_nonneg (by positivity), mul_pow, pow_mul (2 : ℝ), show (2 : ℝ) ^ 2 = 4 by norm_num]
  calc 2 * (k : ℝ) * liClockThetaGeneratorCoeff k ≤
      4 ^ k * (Real.exp (32 / (303 * R ^ 2)) * R ^ (2 * k)) :=
        mul_le_mul h4 hc hcpos.le (by positivity)
    _ = _ := by ring

/-- `t K(t) = Σ_k 2k c_k t^{2k}/(2k)!`. -/
theorem id_mul_liClockThetaKernel_eq (t : ℝ) :
    t * liClockThetaKernel t =
      evenFactorialSeries (fun k => 2 * (k : ℝ) * liClockThetaGeneratorCoeff k) t := by
  have h := hasSum_id_mul_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockThetaKernelCoeff t
  unfold liClockThetaKernel
  rw [← h.tsum_eq]
  unfold evenFactorialSeries
  refine tsum_congr fun k => ?_
  rcases k with _ | k
  · simp
  · simp only [Nat.add_sub_cancel]

private theorem tK_bounds {p : ℝ} (hp : 0 < p) :
    ∀ k : ℕ, |2 * (k : ℝ) * liClockThetaGeneratorCoeff k| ≤
      Real.exp (32 / (303 * (p / 4) ^ 2)) * (p / 2) ^ (2 * k) := fun k => by
  have := abs_two_mul_coeff_le (show 0 < p / 4 by positivity) k
  rwa [show 2 * (p / 4) = p / 2 by ring] at this

theorem integrableOn_exp_mul_id_mul_liClockThetaKernel {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => Real.exp (-(p * t)) * (t * liClockThetaKernel t)) (Ioi 0) := by
  have hb := tK_bounds hp
  have ha₀ : GeometricCoeffBound (fun k => 2 * (k : ℝ) * liClockThetaGeneratorCoeff k)
      (Real.exp (32 / (303 * (p / 4) ^ 2))) ((p / 2) ^ 2) := fun k => by
    rw [← pow_mul]; exact hb k
  have h := integrableOn_borelSeries_mul_exp_neg (geometricCoeffBound_evenSpread_of_le
    (half_pos hp) hb) (by linarith : p / 2 < p)
  rw [← evenFactorialSeries_eq_borelSeries (by positivity) ha₀] at h
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [id_mul_liClockThetaKernel_eq, mul_comm]

/-- `(tK)^(p) = Φ'(1/p)/p²`. -/
theorem integral_exp_mul_id_mul_liClockThetaKernel {p : ℝ} (hp : 0 < p) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * (t * liClockThetaKernel t) =
      liClockThetaGeneratorRealDeriv p⁻¹ / p ^ 2 := by
  have hb := tK_bounds hp
  have ha₀ : GeometricCoeffBound (fun k => 2 * (k : ℝ) * liClockThetaGeneratorCoeff k)
      (Real.exp (32 / (303 * (p / 4) ^ 2))) ((p / 2) ^ 2) := fun k => by
    rw [← pow_mul]; exact hb k
  have hL := hasSum_integral_Ioi_evenFactorialSeries_mul_exp_neg (by positivity) ha₀
    (geometricCoeffBound_evenSpread_of_le (half_pos hp) hb) (by positivity) (by linarith : p / 2 < p)
  rw [← hasSum_nat_add_iff' 1] at hL
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, mul_zero, zero_mul,
    sub_zero] at hL
  have hΦ : HasSum (fun j : ℕ => liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j *
      p⁻¹ ^ (2 * j + 1)) (liClockThetaGeneratorRealDeriv p⁻¹) := by
    have hs := (summable_liClockThetaGeneratorRealDeriv_div p⁻¹).mul_left p⁻¹
    have hs' : Summable fun j : ℕ => liClockThetaMomentRatio j * liClockThetaGeneratorCoeff j *
        p⁻¹ ^ (2 * j + 1) := hs.congr fun j => by ring
    exact hs'.hasSum
  have hΦ2 := hΦ.div_const (p ^ 2)
  have he : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * (t * liClockThetaKernel t) =
      ∫ t in Ioi (0 : ℝ), evenFactorialSeries (fun k => 2 * (k : ℝ) * liClockThetaGeneratorCoeff k) t *
        Real.exp (-(p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [id_mul_liClockThetaKernel_eq, mul_comm]
  rw [he]
  refine hL.unique (hΦ2.congr_fun fun j => ?_)
  rw [liClockThetaMomentRatio_mul_coeff, inv_pow, show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring,
    pow_add, mul_inv]
  push_cast
  ring

private theorem complex_integral_eq_ofReal (p : ℝ) (f : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * f t : ℝ) : ℂ) := by
  have h1 : ∫ t in Ioi (0 : ℝ), Complex.exp (-((p : ℂ) * t)) * (f t : ℂ) =
      ∫ t in Ioi (0 : ℝ), ((Real.exp (-(p * t)) * f t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by push_cast; ring_nf
  rw [h1]
  exact integral_ofReal

/-- The integrated Volterra identity `P + P ⋆ K = tK` on `t ≥ 0`. -/
theorem liEvenCrossActualClockPrimitive_add_volterraConv {t : ℝ} (ht : 0 ≤ t) :
    P t + volterraConv P liClockThetaKernel t = t * liClockThetaKernel t := by
  have h := liEvenCrossActualClockPrimitive_volterra ht
  simp only [deriv_liEvenCrossActualClockBorelKernel_eq] at h
  rw [volterraConv_comm]
  unfold volterraConv
  rw [intervalIntegral.integral_congr (g := fun s => P s * liClockThetaKernel (t - s))
    fun s _ => mul_comm _ _]
  exact h

/-- **Integrated Laplace law (P9).**  `P̂(p) = Φ'(1/p)/(p² Φ(1/p))` for `p > β`. -/
theorem integral_exp_mul_liEvenCrossActualClockPrimitive {p : ℝ} (hp : β < p) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * P t =
      liClockThetaGeneratorRealDeriv p⁻¹ / (p ^ 2 * liClockThetaGeneratorReal p⁻¹) := by
  have hp0 : 0 < p := by linarith [liEvenCrossActualClockMaxGrowthRate_nonneg]
  have hPc := continuous_liEvenCrossActualClockPrimitive
  have hK := continuous_liClockThetaKernel
  have hPi : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |P t|) (Ioi 0) := by
    simpa using integrableOn_exp_mul_abs_liEvenCrossActualClockPrimitive hp
  have hKi : IntegrableOn (fun t => Real.exp (-((p : ℂ).re * t)) * |liClockThetaKernel t|)
      (Ioi 0) := by
    simp only [Complex.ofReal_re]
    refine (integrableOn_liClockThetaKernel_mul_exp_neg hp0).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    rw [abs_of_nonneg (liClockThetaKernel_nonneg (le_of_lt ht)), mul_comm]
  have hconv := integral_Ioi_cexp_mul_volterraConv hPc hK hPi hKi
  rw [complex_integral_eq_ofReal, complex_integral_eq_ofReal, complex_integral_eq_ofReal,
    ← Complex.ofReal_mul] at hconv
  have hreal := Complex.ofReal_injective hconv
  have hsub : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * volterraConv P liClockThetaKernel t =
      (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * (t * liClockThetaKernel t)) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * P t := by
    rw [← integral_sub (integrableOn_exp_mul_id_mul_liClockThetaKernel hp0)
      (integrableOn_exp_mul_liEvenCrossActualClockPrimitive hp)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have := liEvenCrossActualClockPrimitive_add_volterraConv (le_of_lt ht)
    rw [← this]; ring
  rw [hsub, integral_exp_mul_id_mul_liClockThetaKernel hp0] at hreal
  have hKΦ := one_add_integral_kernel_eq hp0
  have hΦ : 0 < liClockThetaGeneratorReal p⁻¹ := by linarith [one_le_liClockThetaGeneratorReal p⁻¹]
  rw [eq_div_iff (by positivity), ← hKΦ]
  have hp2 : p ^ 2 ≠ 0 := by positivity
  field_simp at hreal ⊢
  linear_combination -hreal

/-! ## Dominated differentiation of the moments -/

/-- `M_n' = -M_{n+1}` on `p > β`. -/
theorem hasDerivAt_liClockPrimitiveLaplaceMoment (n : ℕ) {p : ℝ} (hp : β < p) :
    HasDerivAt (liClockPrimitiveLaplaceMoment n) (-liClockPrimitiveLaplaceMoment (n + 1) p) p := by
  set q₀ := (p + β) / 2
  have hq₀ : β < q₀ := by simp only [q₀]; linarith
  have hq₀p : q₀ < p := by simp only [q₀]; linarith
  have hbound := (integrableOn_liClockPrimitiveLaplaceMoment (n + 1) hq₀).abs
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (x t : ℝ) => t ^ n * Real.exp (-(x * t)) * (P t / t))
    (F' := fun (x t : ℝ) => -(t ^ (n + 1) * Real.exp (-(x * t)) * (P t / t)))
    (x₀ := p) (s := Ioi q₀) (bound := fun t => |t ^ (n + 1) * Real.exp (-(q₀ * t)) * (P t / t)|)
    (Ioi_mem_nhds hq₀p)
    (Eventually.of_forall fun x => (measurable_moment_integrand n x).aestronglyMeasurable)
    (integrableOn_liClockPrimitiveLaplaceMoment n hp)
    ((measurable_moment_integrand (n + 1) p).neg.aestronglyMeasurable)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht x hx => by
      have ht0 : 0 < t := ht
      simp only [norm_neg, Real.norm_eq_abs, abs_mul, Real.abs_exp]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        (abs_nonneg _)
      exact Real.exp_le_exp.2 (by nlinarith [show q₀ < x from hx]))
    hbound
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ x _ => by
      have hd := ((hasDerivAt_id' x).mul_const t).fun_neg.exp
      exact ((hd.const_mul (t ^ n)).mul_const (P t / t)).congr_deriv (by ring))
  have he : (∫ t in Ioi (0 : ℝ), -(t ^ (n + 1) * Real.exp (-(p * t)) * (P t / t))) =
      -liClockPrimitiveLaplaceMoment (n + 1) p := by
    rw [integral_neg]; rfl
  rw [← he]
  exact h.2

theorem liClockPrimitiveLaplaceMoment_one_eq {p : ℝ} (hp : β < p) :
    liClockPrimitiveLaplaceMoment 1 p =
      liClockThetaGeneratorRealDeriv p⁻¹ / (p ^ 2 * liClockThetaGeneratorReal p⁻¹) := by
  rw [← integral_exp_mul_liEvenCrossActualClockPrimitive hp]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from ht).ne'
  field_simp

theorem tendsto_liClockPrimitiveLaplaceMoment_zero :
    Tendsto (liClockPrimitiveLaplaceMoment 0) atTop (𝓝 0) := by
  have hbound := (integrableOn_liClockPrimitiveLaplaceMoment 0 (show β < 1 by
    linarith [liEvenCrossActualClockMaxGrowthRate_lt])).abs
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (l := atTop) (F := fun (x t : ℝ) => t ^ 0 * Real.exp (-(x * t)) * (P t / t))
    (f := fun _ => 0) (fun t => |t ^ 0 * Real.exp (-(1 * t)) * (P t / t)|)
    (Eventually.of_forall fun x => (measurable_moment_integrand 0 x).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      simp only [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
        (abs_nonneg _)
      exact Real.exp_le_exp.2 (by nlinarith))
    hbound
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
      have ht0 : 0 < t := ht
      have he : Tendsto (fun x : ℝ => Real.exp (-(x * t))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const ht0)
      have := (he.const_mul (t ^ 0)).mul_const (P t / t)
      simpa using this)
  simp only [integral_zero] at h
  exact h

/-! ## The logarithmic transform -/

theorem liClockThetaGeneratorReal_zero : liClockThetaGeneratorReal 0 = 1 := by
  unfold liClockThetaGeneratorReal
  rw [tsum_eq_single 0 fun j hj => by simp [hj]]
  simp [liClockThetaGeneratorCoeff_zero]

theorem continuous_liClockThetaGeneratorReal : Continuous liClockThetaGeneratorReal :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_liClockThetaGeneratorReal x).continuousAt

theorem one_lt_liClockThetaGeneratorReal {x : ℝ} (hx : x ≠ 0) : 1 < liClockThetaGeneratorReal x := by
  have h := sum_le_hasSum (Finset.range 2)
    (fun j _ => mul_nonneg (liClockThetaGeneratorCoeff_pos j).le (by rw [pow_mul]; positivity))
    (summable_liClockThetaGeneratorReal_term x).hasSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, liClockThetaGeneratorCoeff_zero,
    mul_zero, pow_zero, mul_one] at h
  have hc := liClockThetaGeneratorCoeff_pos 1
  have hx2 : 0 < liClockThetaGeneratorCoeff 1 * x ^ 2 := mul_pos hc (by positivity)
  unfold liClockThetaGeneratorReal
  linarith

theorem hasDerivAt_log_liClockThetaGeneratorReal_inv {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun q => Real.log (liClockThetaGeneratorReal q⁻¹))
      (-(liClockThetaGeneratorRealDeriv p⁻¹ / (p ^ 2 * liClockThetaGeneratorReal p⁻¹))) p := by
  have hΦ : 0 < liClockThetaGeneratorReal p⁻¹ := by linarith [one_le_liClockThetaGeneratorReal p⁻¹]
  have h := ((hasDerivAt_liClockThetaGeneratorReal p⁻¹).comp p (hasDerivAt_inv hp)).log hΦ.ne'
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  field_simp

/-- **Logarithmic transform (P10).**  `∫_0^∞ e^{-pt} P(t)/t dt = log Φ(1/p)` for `p > β`. -/
theorem log_liClockThetaGeneratorReal_inv_eq {p : ℝ} (hp : β < p) :
    Real.log (liClockThetaGeneratorReal p⁻¹) = liClockPrimitiveLaplaceMoment 0 p := by
  set G := fun q => Real.log (liClockThetaGeneratorReal q⁻¹) - liClockPrimitiveLaplaceMoment 0 q
  have hG : ∀ q, β < q → HasDerivAt G 0 q := by
    intro q hq
    have h := (hasDerivAt_log_liClockThetaGeneratorReal_inv (show q ≠ 0 by
      linarith [liEvenCrossActualClockMaxGrowthRate_nonneg])).sub
      (hasDerivAt_liClockPrimitiveLaplaceMoment 0 hq)
    rw [liClockPrimitiveLaplaceMoment_one_eq hq] at h
    exact h.congr_deriv (by ring)
  have hconst : ∀ b, p ≤ b → G b = G p := by
    intro b hb
    have := constant_of_has_deriv_right_zero (f := G) (a := p) (b := b)
      (fun x hx => (hG x (hp.trans_le hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => (hG x (hp.trans_le hx.1)).hasDerivWithinAt)
    exact this b ⟨hb, le_rfl⟩
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun q : ℝ => Real.log (liClockThetaGeneratorReal q⁻¹)) atTop (𝓝 0) := by
      have hc : Tendsto (fun q : ℝ => liClockThetaGeneratorReal q⁻¹) atTop (𝓝 1) := by
        rw [← liClockThetaGeneratorReal_zero]
        exact (continuous_liClockThetaGeneratorReal.tendsto 0).comp tendsto_inv_atTop_zero
      have := (Real.continuousAt_log one_ne_zero).tendsto.comp hc
      rwa [Real.log_one] at this
    have := h1.sub tendsto_liClockPrimitiveLaplaceMoment_zero
    rwa [sub_zero] at this
  have hlim' : Tendsto G atTop (𝓝 (G p)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop p] with b hb
      exact (hconst b hb).symm)
  have := tendsto_nhds_unique hlim' hlim
  simp only [G] at this
  linarith

theorem log_liClockThetaGeneratorReal_inv_pos {p : ℝ} (hp : 0 < p) :
    0 < Real.log (liClockThetaGeneratorReal p⁻¹) :=
  Real.log_pos (one_lt_liClockThetaGeneratorReal (inv_ne_zero hp.ne'))

/-- **All-order moments (P11).**  `(d/dp)^n log Φ(1/p) = (-1)^n M_n(p)` for `p > β`. -/
theorem iteratedDeriv_log_liClockThetaGeneratorReal_inv (n : ℕ) {p : ℝ} (hp : β < p) :
    iteratedDeriv n (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) p =
      (-1) ^ n * liClockPrimitiveLaplaceMoment n p := by
  induction n generalizing p with
  | zero => simpa using log_liClockThetaGeneratorReal_inv_eq hp
  | succ n ih =>
    have hev : iteratedDeriv n (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) =ᶠ[𝓝 p]
        fun q => (-1) ^ n * liClockPrimitiveLaplaceMoment n q := by
      filter_upwards [Ioi_mem_nhds hp] with q hq
      exact ih hq
    rw [iteratedDeriv_succ, hev.deriv_eq,
      ((hasDerivAt_liClockPrimitiveLaplaceMoment n hp).const_mul ((-1) ^ n)).deriv, pow_succ]
    ring

theorem neg_one_pow_mul_iteratedDeriv_log_liClockThetaGeneratorReal_inv (n : ℕ) {p : ℝ}
    (hp : β < p) :
    (-1) ^ n * iteratedDeriv n (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) p =
      ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(p * t)) * (P t / t) := by
  rw [iteratedDeriv_log_liClockThetaGeneratorReal_inv n hp, ← mul_assoc, ← pow_add, ← two_mul,
    pow_mul]
  simp [liClockPrimitiveLaplaceMoment]

/-! ## Complete monotonicity is equivalent to RH -/

/-- **RH criterion (P14).**  RH holds iff `log Φ(1/p)` is completely monotone on `p > 1/300`. -/
theorem rh_iff_completelyMonotone_log_liClockThetaGeneratorReal_inv :
    RiemannHypothesis ↔ ∀ n : ℕ, ∀ p : ℝ, 1 / 300 < p →
      0 ≤ (-1) ^ n * iteratedDeriv n (fun q => Real.log (liClockThetaGeneratorReal q⁻¹)) p := by
  constructor
  · intro hRH n p hp
    rw [neg_one_pow_mul_iteratedDeriv_log_liClockThetaGeneratorReal_inv n
      (liEvenCrossActualClockMaxGrowthRate_lt_of_lt hp)]
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have := liEvenCrossActualClockPrimitive_nonneg_of_rh hRH t
    positivity
  · intro h
    refine (liEvenCrossActualClockPrimitive_rh_criteria).1.2 fun t ht => ?_
    rcases ht.eq_or_lt with rfl | ht
    · simp [liEvenCrossActualClockPrimitive]
    · have hf : ContinuousAt (fun s => P s / s) t :=
        (continuous_liEvenCrossActualClockPrimitive.continuousAt).div continuousAt_id ht.ne'
      have hnn := nonneg_of_laplaceMoments_nonneg ht hf
        (fun n p hp => integrableOn_liClockPrimitiveLaplaceMoment n
          (liEvenCrossActualClockMaxGrowthRate_lt_of_lt hp))
        (fun n p hp => by
          rw [← neg_one_pow_mul_iteratedDeriv_log_liClockThetaGeneratorReal_inv n
            (liEvenCrossActualClockMaxGrowthRate_lt_of_lt hp)]
          exact h n p hp)
      have := mul_nonneg ht.le hnn
      rwa [mul_div_cancel₀ _ ht.ne'] at this

/-- Equivalently, RH holds iff every weighted Laplace moment of `P/t` is nonnegative. -/
theorem rh_iff_liClockPrimitiveLaplaceMoment_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, ∀ p : ℝ, 1 / 300 < p → 0 ≤ liClockPrimitiveLaplaceMoment n p := by
  rw [rh_iff_completelyMonotone_log_liClockThetaGeneratorReal_inv]
  refine forall_congr' fun n => forall_congr' fun p => imp_congr_right fun hp => ?_
  rw [neg_one_pow_mul_iteratedDeriv_log_liClockThetaGeneratorReal_inv n
    (liEvenCrossActualClockMaxGrowthRate_lt_of_lt hp)]
  rfl

end RHTower
