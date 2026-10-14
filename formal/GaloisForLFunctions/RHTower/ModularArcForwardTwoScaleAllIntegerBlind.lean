import GaloisForLFunctions.RHTower.ModularArcTwoScaleStripEdgeVanishing

/-!
# Forward two-scale modular arc witnesses: all-integer blindness and quadratic strip-edge vanishing

In `ModularArcTwoScaleHyperbolicWitness` and `ModularArcTwoScaleStripEdgeVanishing`, we constructed
the two-scale hyperbolic pole-filtered modular arc witness `W_{k,ν} = arcLineTwoScaleVector k ν`,
which is strictly self-reciprocal (`W(1/x) = |x| W(x)`), strictly positive definite on the critical
line, blind along the infinite `k⁴`-sublattice `arcFreq (k⁴(m+1) − 1)` (`m ∈ ℕ`), and vanishes
quadratically `O((1/2 − l)²)` at the critical strip edge `l → (1/2)⁻`.

In this module we apply the forward dilation `D_{4 log k}` (`x ↦ x / k⁴`, weighted by `k⁻²`) to
`W_{k,ν}`, defining:

`F_{k,ν}(x) = k⁻² W_{k,ν}(x / k⁴)`  (`arcLineForwardTwoScaleVector k ν`),

with derivative `F_{k,ν}'(x) = k⁻⁶ W_{k,ν}'(x / k⁴)` (`arcLineForwardTwoScaleDeriv k ν`) and
log-scale profile `e^{v/2} F_{k,ν}(e^v) = W_{k,ν}^{prof}(v − 4 log k)`
(`arcLineForwardTwoScaleProfile k ν v`).

Because `W_{k,ν}'` is identically blind on the `k⁴`-sublattice `arcFreq (k⁴(n+1) − 1)` and
rescaling `x ↦ x / k⁴` maps every positive integer frequency `arcFreq n = 2π(n+1)` onto
`arcFreq (k⁴(n+1) − 1)`, while shifting `v ↦ v − 4 log k` multiplies the strip Laplace/Mellin
transform by the bounded factor `e^{4l log k} ≤ k²` on `l ∈ [0, 1/2)`, `F_{k,ν}` simultaneously
achieves:
1. **Simultaneous blindness at EVERY positive integer frequency `arcFreq n = 2π(n+1)` (`∀ n ∈ ℕ`)**,
   both sine and cosine (`integral_arcLineForwardTwoScaleDeriv_mul_sin_eq_zero`,
   `integral_arcLineForwardTwoScaleDeriv_mul_cos_eq_zero`);
2. **Quadratic strip-edge vanishing `O((1/2 − l)²)` and double-pole divided-difference vanishing**
   `(∫ e^{lv} F_{k,ν}^{prof}(v) dv) / (1/2 − l) → 0` as `l → (1/2)⁻`
   (`abs_integral_exp_mul_arcLineForwardTwoScaleProfile_le`,
   `tendsto_div_sub_half_integral_exp_mul_arcLineForwardTwoScaleProfile_nhdsWithin`);
3. **Full two-sided `O(e^{−3|v|/2})` Weil decay class, zero mean `∫ F_{k,ν} = 0`, `k⁴`-centered
   inversion covariance `F_{k,ν}(k⁸ / x) = (|x| / k⁴) F_{k,ν}(x)`, and strict critical-line
   positive definiteness after centering at `4 log k`.**
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Definition and calculus of `arcLineForwardTwoScaleVector` -/

/-- The forward `4 log k`-dilated two-scale hyperbolic modular arc witness:
`F_{k,ν}(x) = k⁻² · arcLineTwoScaleVector k ν (x / k⁴)`. -/
def arcLineForwardTwoScaleVector (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ 2)⁻¹ * arcLineTwoScaleVector k ν (x * ((k : ℝ) ^ 4)⁻¹)

/-- Its derivative `F_{k,ν}'(x) = k⁻⁶ · arcLineTwoScaleDeriv k ν (x / k⁴)`. -/
def arcLineForwardTwoScaleDeriv (k : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  ((k : ℝ) ^ 6)⁻¹ * arcLineTwoScaleDeriv k ν (x * ((k : ℝ) ^ 4)⁻¹)

/-- Its log-scale profile `arcLineTwoScaleProfile k ν (v − 4 log k)`. -/
def arcLineForwardTwoScaleProfile (k : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  arcLineTwoScaleProfile k ν (v - 4 * Real.log k)

theorem hasDerivAt_arcLineForwardTwoScaleVector (k : ℕ) (ν : Measure ArcParam)
    [IsFiniteMeasure ν] (x : ℝ) :
    HasDerivAt (arcLineForwardTwoScaleVector k ν) (arcLineForwardTwoScaleDeriv k ν x) x := by
  have hc : HasDerivAt (fun x' : ℝ => x' * ((k : ℝ) ^ 4)⁻¹) (((k : ℝ) ^ 4)⁻¹) x := by
    simpa using (hasDerivAt_id x).mul_const (((k : ℝ) ^ 4)⁻¹)
  have h := ((hasDerivAt_arcLineTwoScaleVector k ν
    (x * ((k : ℝ) ^ 4)⁻¹)).comp x hc).const_mul (((k : ℝ) ^ 2)⁻¹)
  refine h.congr_deriv ?_
  unfold arcLineForwardTwoScaleDeriv
  ring

theorem arcLineForwardTwoScaleVector_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineForwardTwoScaleVector k ν (-x) = arcLineForwardTwoScaleVector k ν x := by
  unfold arcLineForwardTwoScaleVector
  rw [neg_mul, arcLineTwoScaleVector_neg_of_map_arcNeg k hν]

theorem arcLineForwardTwoScaleDeriv_neg_of_map_arcNeg (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineForwardTwoScaleDeriv k ν (-x) = -arcLineForwardTwoScaleDeriv k ν x := by
  unfold arcLineForwardTwoScaleDeriv
  rw [neg_mul, arcLineTwoScaleDeriv_neg_of_map_arcNeg k hν, mul_neg]

/-- **`k⁴`-centered inversion covariance**: `F_{k,ν}(k⁸ / x) = (|x| / k⁴) F_{k,ν}(x)` for `x ≠ 0`. -/
theorem arcLineForwardTwoScaleVector_inv_scaled {k : ℕ} (hk : 1 ≤ k) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineForwardTwoScaleVector k ν ((k : ℝ) ^ 8 / x) =
      |x| / (k : ℝ) ^ 4 * arcLineForwardTwoScaleVector k ν x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hxne : x * ((k : ℝ) ^ 4)⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero (pow_ne_zero 4 hkne))
  unfold arcLineForwardTwoScaleVector
  have e : (k : ℝ) ^ 8 / x * ((k : ℝ) ^ 4)⁻¹ = 1 / (x * ((k : ℝ) ^ 4)⁻¹) := by
    field_simp
  rw [e, arcLineTwoScaleVector_inv hk ν hxne, abs_mul,
    abs_of_pos (inv_pos.mpr (pow_pos hkpos 4))]
  ring

theorem exp_half_mul_arcLineForwardTwoScaleVector {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) (v : ℝ) :
    Real.exp (v / 2) * arcLineForwardTwoScaleVector k ν (Real.exp v) =
      arcLineForwardTwoScaleProfile k ν v := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  unfold arcLineForwardTwoScaleVector arcLineForwardTwoScaleProfile
  have he4 : ((k : ℝ) ^ 4)⁻¹ = Real.exp (-(4 * Real.log k)) := by
    rw [Real.exp_neg, show (4 : ℝ) * Real.log k = ((4 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have he2 : ((k : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log k)) := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have e1 : Real.exp v * ((k : ℝ) ^ 4)⁻¹ = Real.exp (v - 4 * Real.log k) := by
    rw [he4, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * ((k : ℝ) ^ 2)⁻¹ = Real.exp ((v - 4 * Real.log k) / 2) := by
    rw [he2, ← Real.exp_add]; congr 1; ring
  rw [e1, ← mul_assoc, e2, exp_half_mul_arcLineTwoScaleVector hk]

/-! ### Full two-sided `O(e^{−3|v|/2})` Weil decay class, integrability, and zero mean -/

theorem abs_arcLineForwardTwoScaleProfile_le {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) (v : ℝ) :
    |arcLineForwardTwoScaleProfile k ν v| ≤
      10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 12 * Real.exp (-(3 * |v| / 2)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  unfold arcLineForwardTwoScaleProfile
  have hprof := abs_arcLineTwoScaleProfile_le hk hν (v - 4 * Real.log k)
  have hexp6 : Real.exp (6 * Real.log k) = (k : ℝ) ^ 6 := by
    rw [show (6 : ℝ) * Real.log k = ((6 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have hshift : Real.exp (-(3 * |v - 4 * Real.log k| / 2)) ≤
      (k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2)) := by
    rw [← hexp6, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs : |v| - |4 * Real.log k| ≤ |v - 4 * Real.log k| := abs_sub_abs_le_abs_sub v _
    have hlog : |4 * Real.log k| = 4 * Real.log k := abs_of_nonneg (by positivity)
    linarith
  have hC0 : 0 ≤ 10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  calc |arcLineTwoScaleProfile k ν (v - 4 * Real.log k)|
      ≤ 10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 *
          Real.exp (-(3 * |v - 4 * Real.log k| / 2)) := hprof
    _ ≤ 10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 6 *
          ((k : ℝ) ^ 6 * Real.exp (-(3 * |v| / 2))) :=
        mul_le_mul_of_nonneg_left hshift hC0
    _ = 10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 12 * Real.exp (-(3 * |v| / 2)) := by
        ring

theorem integrable_arcLineForwardTwoScaleVector {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Integrable (arcLineForwardTwoScaleVector k ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineTwoScaleVector hk hν).comp_mul_right'
    (inv_ne_zero (pow_ne_zero 4 hkpos.ne'))).const_mul (((k : ℝ) ^ 2)⁻¹)

theorem integrable_arcLineForwardTwoScaleDeriv {k : ℕ} (hk : 1 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν] :
    Integrable (arcLineForwardTwoScaleDeriv k ν) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  exact ((integrable_arcLineTwoScaleDeriv hk ν).comp_mul_right'
    (inv_ne_zero (pow_ne_zero 4 hkpos.ne'))).const_mul (((k : ℝ) ^ 6)⁻¹)

theorem integral_arcLineForwardTwoScaleVector_eq_zero {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam}
    [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineForwardTwoScaleVector k ν x = 0 := by
  unfold arcLineForwardTwoScaleVector
  rw [integral_const_mul, Measure.integral_comp_mul_right
    (arcLineTwoScaleVector k ν) (((k : ℝ) ^ 4)⁻¹),
    integral_arcLineTwoScaleVector_eq_zero hk hν, smul_zero, mul_zero]

theorem arcLineForwardTwoScaleProfile_add_four_log (k : ℕ) (ν : Measure ArcParam) (v : ℝ) :
    arcLineForwardTwoScaleProfile k ν (v + 4 * Real.log k) =
      arcLineTwoScaleProfile k ν v := by
  unfold arcLineForwardTwoScaleProfile
  rw [add_sub_cancel_right]

/-- **Strict positive definiteness of the `4 log k`-centered log-profile on the critical line.** -/
theorem integral_cos_mul_arcLineForwardTwoScaleProfile_add_pos {k : ℕ} (hk : 2 ≤ k)
    (ν : Measure ArcParam) [IsFiniteMeasure ν]
    (hpd : ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * arcPoissonProfile ν v) (τ : ℝ) :
    0 < ∫ v, Real.cos (τ * v) * arcLineForwardTwoScaleProfile k ν (v + 4 * Real.log k) := by
  simp_rw [arcLineForwardTwoScaleProfile_add_four_log]
  exact integral_cos_mul_arcLineTwoScaleProfile_pos hk ν hpd τ

/-! ### Simultaneous blindness at ALL positive integer frequencies `arcFreq n = 2π(n+1)` (`n ∈ ℕ`) -/

theorem integral_arcLineForwardTwoScaleDeriv_mul_cos_eq_zero (k : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (c : ℝ) :
    ∫ x, arcLineForwardTwoScaleDeriv k ν x * Real.cos (c * x) = 0 := by
  have h := integral_neg_eq_self
    (fun x : ℝ => arcLineForwardTwoScaleDeriv k ν x * Real.cos (c * x)) volume
  have e : (fun x : ℝ => arcLineForwardTwoScaleDeriv k ν (-x) * Real.cos (c * -x)) =
      fun x => -(arcLineForwardTwoScaleDeriv k ν x * Real.cos (c * x)) := by
    funext x
    rw [arcLineForwardTwoScaleDeriv_neg_of_map_arcNeg k hν, mul_neg, Real.cos_neg, neg_mul]
  rw [e, integral_neg] at h
  linarith

/-- **Simultaneous sine blindness at EVERY positive integer frequency `arcFreq n = 2π(n+1)`.**
Rescaling `t = x / k⁴` maps `arcFreq n` onto `arcFreq (k⁴(n+1) − 1)`, which lies on the
`k⁴`-blind sublattice of `arcLineTwoScaleDeriv k ν`. -/
theorem integral_arcLineForwardTwoScaleDeriv_mul_sin_eq_zero {ν : Measure ArcParam}
    [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ∫ x, arcLineForwardTwoScaleDeriv k ν x * Real.sin (arcFreq n * x) = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hk4 : 1 ≤ k ^ 4 := Nat.one_le_pow 4 k hk
  have hfreq : arcFreq n * ((k : ℝ) ^ 4) = arcFreq (k ^ 4 * (n + 1) - 1) := by
    rw [Nat.mul_comm (k ^ 4) (n + 1), ← arcFreq_mul_nat hk4 n]
    push_cast; ring
  have e : (fun x => arcLineForwardTwoScaleDeriv k ν x * Real.sin (arcFreq n * x)) = fun x =>
      ((k : ℝ) ^ 6)⁻¹ * (arcLineTwoScaleDeriv k ν (x * ((k : ℝ) ^ 4)⁻¹) *
        Real.sin (arcFreq (k ^ 4 * (n + 1) - 1) * (x * ((k : ℝ) ^ 4)⁻¹))) := by
    funext x
    unfold arcLineForwardTwoScaleDeriv
    rw [← hfreq]
    have hx : arcFreq n * (k : ℝ) ^ 4 * (x * ((k : ℝ) ^ 4)⁻¹) = arcFreq n * x := by
      field_simp
    rw [hx]; ring
  rw [e, integral_const_mul, Measure.integral_comp_mul_right
    (fun t => arcLineTwoScaleDeriv k ν t *
      Real.sin (arcFreq (k ^ 4 * (n + 1) - 1) * t)) (((k : ℝ) ^ 4)⁻¹),
    integral_arcLineTwoScaleDeriv_mul_sin_pow4_mul_eq_zero hblind hk n,
    smul_zero, mul_zero]

/-! ### Quadratic strip-edge vanishing and double-pole cancellation for `arcLineForwardTwoScaleProfile` -/

theorem integral_exp_mul_arcLineForwardTwoScaleProfile (k : ℕ) (ν : Measure ArcParam) (l : ℝ) :
    ∫ v, Real.exp (l * v) * arcLineForwardTwoScaleProfile k ν v =
      Real.exp (l * (4 * Real.log k)) *
        ∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v := by
  unfold arcLineForwardTwoScaleProfile
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.exp (l * v) * arcLineTwoScaleProfile k ν (v - 4 * Real.log k))
    (4 * Real.log k), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [add_sub_cancel_right,
    show l * (v + 4 * Real.log k) = l * (4 * Real.log k) + l * v by ring, Real.exp_add]
  ring

/-- **Quadratic strip-edge vanishing bound for `arcLineForwardTwoScaleProfile k ν`.** -/
theorem abs_integral_exp_mul_arcLineForwardTwoScaleProfile_le {k : ℕ} (hk : 1 ≤ k)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineForwardTwoScaleProfile k ν v| ≤
      20 * ν.real univ * (k : ℝ) ^ 2 * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hk)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hb : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hexp2 : Real.exp (2 * Real.log k) = (k : ℝ) ^ 2 := by
    rw [show (2 : ℝ) * Real.log k = ((2 : ℕ) : ℝ) * Real.log k by norm_num,
      Real.exp_nat_mul, Real.exp_log hkpos]
  have hexp_le : Real.exp (l * (4 * Real.log k)) ≤ (k : ℝ) ^ 2 := by
    rw [← hexp2]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rw [integral_exp_mul_arcLineForwardTwoScaleProfile, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hW := abs_integral_exp_mul_arcLineTwoScaleProfile_le hk hν hl0 hl
  have hRHS0 : 0 ≤ 20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 := by
    have := measureReal_nonneg (μ := ν) (s := univ)
    positivity
  calc Real.exp (l * (4 * Real.log k)) *
        |∫ v, Real.exp (l * v) * arcLineTwoScaleProfile k ν v|
      ≤ (k : ℝ) ^ 2 * (20 * ν.real univ * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2) :=
        mul_le_mul hexp_le hW (abs_nonneg _) (by positivity)
    _ = 20 * ν.real univ * (k : ℝ) ^ 2 * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 := by ring

/-- **Double-pole divided-difference bound for `arcLineForwardTwoScaleProfile k ν`.** -/
theorem abs_div_sub_half_integral_exp_mul_arcLineForwardTwoScaleProfile_le {k : ℕ} (hk : 1 ≤ k)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |(∫ v, Real.exp (l * v) * arcLineForwardTwoScaleProfile k ν v) / (1 / 2 - l)| ≤
      20 * ν.real univ * (k : ℝ) ^ 2 * (Real.log k) ^ 3 * (1 / 2 - l) := by
  have hκ : 0 < 1 / 2 - l := by linarith
  rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
  calc |∫ v, Real.exp (l * v) * arcLineForwardTwoScaleProfile k ν v|
      ≤ 20 * ν.real univ * (k : ℝ) ^ 2 * (Real.log k) ^ 3 * (1 / 2 - l) ^ 2 :=
        abs_integral_exp_mul_arcLineForwardTwoScaleProfile_le hk hν hl0 hl
    _ = 20 * ν.real univ * (k : ℝ) ^ 2 * (Real.log k) ^ 3 * (1 / 2 - l) * (1 / 2 - l) := by
        ring

/-- **Double-pole edge vanishing as `l → (1/2)⁻` for `arcLineForwardTwoScaleProfile k ν`.** -/
theorem tendsto_div_sub_half_integral_exp_mul_arcLineForwardTwoScaleProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineForwardTwoScaleProfile k ν v) / (1 / 2 - l))
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := 20 * ν.real univ * (k : ℝ) ^ 2 * (Real.log k) ^ 3
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  rw [Real.norm_eq_abs]
  exact abs_div_sub_half_integral_exp_mul_arcLineForwardTwoScaleProfile_le hk hν hl.1.le hl.2

/-! ### Master unconditional all-integer-blind quadratic-edge witness theorem -/

/-- **Master unconditional theorem for all-integer-blind quadratic-edge modular arc witnesses.**
For every integer `k ≥ 2`, `F = arcLineForwardTwoScaleVector k ν` is a single fixed function in
the full two-sided `O(e^{−3|v|/2})` Weil decay class (even, integrable with zero mean,
`k⁴`-inversion-covariant, and strictly positive definite on the critical line after centering at
`4 log k`) such that:
1. Its derivative `F'` is **simultaneously blind at EVERY nonzero integer frequency `2π(n+1)`
   (`∀ n ∈ ℕ`)**, both sine and cosine;
2. Its strip Laplace/Mellin transform vanishes quadratically `O((1/2 − l)²)` at `l → (1/2)⁻`, so
   that even its divided difference `(∫ e^{lv} F^{prof}(v) dv) / (1/2 − l)` converges to `0` on
   `𝓝[<] (1/2)` (annihilating both simple and double poles at the critical strip edge). -/
theorem exists_forwardTwoScale_allInteger_blind_quadraticEdge_witness {k : ℕ} (hk : 2 ≤ k) :
    ∃ F F' : ℝ → ℝ,
      (∀ x, HasDerivAt F (F' x) x) ∧ Integrable F ∧ Integrable F' ∧
      (∀ x, F (-x) = F x) ∧ (∀ x, F' (-x) = -F' x) ∧
      (∀ x, x ≠ 0 → F ((k : ℝ) ^ 8 / x) = |x| / (k : ℝ) ^ 4 * F x) ∧
      ∫ x, F x = 0 ∧
      (∃ C, 0 < C ∧ ∀ v, |Real.exp (v / 2) * F (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, F' x * Real.sin (arcFreq n * x) = 0) ∧
      (∀ c : ℝ, ∫ x, F' x * Real.cos (c * x) = 0) ∧
      (∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) *
        (Real.exp ((v + 4 * Real.log k) / 2) * F (Real.exp (v + 4 * Real.log k)))) ∧
      Tendsto (fun l : ℝ =>
        (∫ v, Real.exp (l * v) * (Real.exp (v / 2) * F (Real.exp v))) / (1 / 2 - l))
        (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, hpd⟩ := exists_arcWitness
  have hk1 : 1 ≤ k := by omega
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨arcLineForwardTwoScaleVector k ν, arcLineForwardTwoScaleDeriv k ν,
    hasDerivAt_arcLineForwardTwoScaleVector k ν,
    integrable_arcLineForwardTwoScaleVector hk1 hsym,
    integrable_arcLineForwardTwoScaleDeriv hk1 ν,
    arcLineForwardTwoScaleVector_neg_of_map_arcNeg k hsym,
    arcLineForwardTwoScaleDeriv_neg_of_map_arcNeg k hsym,
    fun x hx => arcLineForwardTwoScaleVector_inv_scaled hk1 ν hx,
    integral_arcLineForwardTwoScaleVector_eq_zero hk1 hsym,
    ⟨10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 12 + 1, ?_, fun v => ?_⟩,
    integral_arcLineForwardTwoScaleDeriv_mul_sin_eq_zero hblind hk1,
    integral_arcLineForwardTwoScaleDeriv_mul_cos_eq_zero k hsym,
    fun τ => ?_,
    ?_⟩
  · have := measureReal_nonneg (μ := ν) (s := univ)
    have := atomMass_nonneg (Real.log k)
    positivity
  · rw [exp_half_mul_arcLineForwardTwoScaleVector hk1]
    calc |arcLineForwardTwoScaleProfile k ν v|
        ≤ 10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 12 *
            Real.exp (-(3 * |v| / 2)) := abs_arcLineForwardTwoScaleProfile_le hk1 hsym v
      _ ≤ (10 * ν.real univ * atomMass (Real.log k) * (k : ℝ) ^ 12 + 1) *
            Real.exp (-(3 * |v| / 2)) := by
          gcongr; linarith
  · simp_rw [exp_half_mul_arcLineForwardTwoScaleVector hk1]
    exact integral_cos_mul_arcLineForwardTwoScaleProfile_add_pos hk ν hpd τ
  · simp_rw [exp_half_mul_arcLineForwardTwoScaleVector hk1]
    exact tendsto_div_sub_half_integral_exp_mul_arcLineForwardTwoScaleProfile_nhdsWithin hk1 hsym

end

end RHTower
