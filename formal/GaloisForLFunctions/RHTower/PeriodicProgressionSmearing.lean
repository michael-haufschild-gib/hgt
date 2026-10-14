import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Positive real part on the critical line with poles on a vertical progression

For real `c > 0` and `r > √2` put

`S(s) = −c·2^{−s} / (1 − r·2^{−s})`   (`progressionSmearer c r`).

* **Dirichlet series** (`hasSum_progressionSmearer`).  On `r·2^{−Re s} < 1`,
  `S(s) = −c Σ_{k≥0} r^k 2^{−(k+1)s}`: a Dirichlet series supported on the powers of `2`.
* **Positivity on the critical line** (`le_re_progressionSmearer`).  With `R = r/√2 > 1`,
  `Re S(½ + it) ≥ (c/r)·R/(R+1)` for every real `t`.  Writing `z = r·2^{−s}` one has
  `S = (c/r)·z/(z − 1)` with `‖z‖ = R`, and `Re (z/(z−1)) = (R² − Re z)/(R² − 2 Re z + 1)`, which
  is at least `R/(R+1)` because `(R − 1)(R + Re z) ≥ 0`.
* **Poles right of the line** (`progressionPole_re`, `mul_cpow_progressionPole`,
  `tendsto_progressionSmearer_residue`).  At `s_k = log r/log 2 + 2πik/log 2` one has
  `r·2^{−s_k} = 1` and `Re s_k > ½`, and `(s − s_k) S(s) → −c/(r log 2)`: a simple pole with
  negative residue at every point of the vertical progression `log₂ r + (2πi/log 2) ℤ`.

* **Exact mass per pole** (`integral_progressionSmearer_period`,
  `integral_re_progressionSmearer_period`).  Over one period `0 ≤ t ≤ 2π/log 2` of the line, which
  contains the ordinate of exactly one pole, `∫ S(½ + it) dt = (c/r)·(2π/log 2) = 2π·c/(r log 2)`:
  the real part of `S` carries `2π` times the absolute residue per pole.  On the circle
  `z = R e^{iθ}` this is `∫_0^{2π} z/(z − 1) dθ = 2π` (`integral_circleMap_div_sub_one`), the
  circle integral of `(z − 1)⁻¹` around the enclosed point `1`.

So positivity of the real part of an integer-supported Dirichlet series on `Re s = ½` does not
exclude poles with negative residue in `Re s > ½`; the poles of `S` form a full vertical
progression, and each of them is spread over the line as positive mass `2π·|residue|`.
-/

open Complex Filter Topology
open scoped Real

noncomputable section

namespace RHTower.PeriodicSmearing

/-- The progression smearer `S(s) = −c·2^{−s} / (1 − r·2^{−s})`. -/
def progressionSmearer (c r : ℝ) (s : ℂ) : ℂ :=
  -(c : ℂ) * (2 : ℂ) ^ (-s) / (1 - (r : ℂ) * (2 : ℂ) ^ (-s))

/-! ## The Möbius bound -/

/-- For `‖z‖ = R > 1`, `R/(R+1) ≤ Re (z/(z−1))`. -/
theorem le_re_div_sub_one {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 1 < R) :
    R / (R + 1) ≤ (z / (z - 1)).re := by
  have hx : |z.re| ≤ R := hz ▸ Complex.abs_re_le_norm z
  have hxR := abs_le.mp hx
  have hsq : z.re ^ 2 + z.im ^ 2 = R ^ 2 := by
    rw [← hz, Complex.sq_norm, Complex.normSq_apply]; ring
  have hden : 0 < (z.re - 1) ^ 2 + z.im ^ 2 := by nlinarith
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  rw [← add_div, le_div_iff₀ (by nlinarith), div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

/-! ## Values on the critical line -/

theorem norm_two_cpow_neg (s : ℂ) : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
  have h := Complex.norm_cpow_eq_rpow_re_of_pos (x := (2 : ℝ)) (by norm_num) (-s)
  simpa using h

theorem norm_two_cpow_neg_line (t : ℝ) :
    ‖(2 : ℂ) ^ (-((1 / 2 : ℂ) + t * I))‖ = (Real.sqrt 2)⁻¹ := by
  rw [norm_two_cpow_neg]
  have hre : ((1 / 2 : ℂ) + t * I).re = 1 / 2 := by simp
  rw [hre, Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num)]

theorem progressionSmearer_eq (c : ℝ) {r : ℝ} (hr : r ≠ 0) (s : ℂ) :
    progressionSmearer c r s =
      ((c / r : ℝ) : ℂ) * ((r * (2 : ℂ) ^ (-s)) / (r * (2 : ℂ) ^ (-s) - 1)) := by
  unfold progressionSmearer
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  by_cases h : (r : ℂ) * (2 : ℂ) ^ (-s) - 1 = 0
  · have h' : 1 - (r : ℂ) * (2 : ℂ) ^ (-s) = 0 := by linear_combination -h
    rw [h, h', div_zero, div_zero, mul_zero]
  · have h' : 1 - (r : ℂ) * (2 : ℂ) ^ (-s) ≠ 0 := fun h0 => h (by linear_combination -h0)
    have hneg : (r : ℂ) * (2 : ℂ) ^ (-s) - 1 = -(1 - (r : ℂ) * (2 : ℂ) ^ (-s)) := by ring
    rw [hneg]
    push_cast
    field_simp

/-- **Positivity on the critical line.**  For `c ≥ 0` and `r > √2`, with `R = r/√2`,
`Re S(½ + it) ≥ (c/r)·R/(R+1)`. -/
theorem le_re_progressionSmearer {c r : ℝ} (hc : 0 ≤ c) (hr : Real.sqrt 2 < r) (t : ℝ) :
    c / r * ((r / Real.sqrt 2) / (r / Real.sqrt 2 + 1)) ≤
      (progressionSmearer c r ((1 / 2 : ℂ) + t * I)).re := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hr0 : 0 < r := hs2.trans hr
  set z : ℂ := r * (2 : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) with hzdef
  have hz : ‖z‖ = r / Real.sqrt 2 := by
    rw [hzdef, norm_mul, norm_two_cpow_neg_line, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, div_eq_mul_inv]
  have hR : 1 < r / Real.sqrt 2 := by rw [lt_div_iff₀ hs2]; linarith
  rw [progressionSmearer_eq c hr0.ne', ← hzdef, Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left (le_re_div_sub_one hz hR) (div_nonneg hc hr0.le)

/-- The real part of `S` on the critical line is strictly positive for `c > 0`, `r > √2`. -/
theorem re_progressionSmearer_pos {c r : ℝ} (hc : 0 < c) (hr : Real.sqrt 2 < r) (t : ℝ) :
    0 < (progressionSmearer c r ((1 / 2 : ℂ) + t * I)).re := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hr0 : 0 < r := hs2.trans hr
  refine lt_of_lt_of_le ?_ (le_re_progressionSmearer hc.le hr t)
  have hR : 0 < r / Real.sqrt 2 := div_pos hr0 hs2
  positivity

/-! ## The Dirichlet series -/

/-- **Dirichlet series on the powers of `2`.**  If `r·2^{−Re s} < 1`, then
`S(s) = −c Σ_{k≥0} r^k 2^{−(k+1)s}`. -/
theorem hasSum_progressionSmearer (c r : ℝ) {s : ℂ} (hs : |r| * (2 : ℝ) ^ (-s.re) < 1) :
    HasSum (fun k : ℕ => -(c : ℂ) * (r : ℂ) ^ k * (2 : ℂ) ^ (((k + 1 : ℕ) : ℂ) * (-s)))
      (progressionSmearer c r s) := by
  have hq : ‖(r : ℂ) * (2 : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, norm_two_cpow_neg, Complex.norm_real, Real.norm_eq_abs]; exact hs
  have hg := (hasSum_geometric_of_norm_lt_one hq).mul_left (-(c : ℂ) * (2 : ℂ) ^ (-s))
  have hf : (fun k : ℕ => -(c : ℂ) * (r : ℂ) ^ k * (2 : ℂ) ^ (((k + 1 : ℕ) : ℂ) * (-s))) =
      fun k : ℕ => -(c : ℂ) * (2 : ℂ) ^ (-s) * ((r : ℂ) * (2 : ℂ) ^ (-s)) ^ k := by
    funext k
    rw [Complex.cpow_nat_mul, mul_pow, pow_succ]
    ring
  have hS : progressionSmearer c r s =
      -(c : ℂ) * (2 : ℂ) ^ (-s) * (1 - (r : ℂ) * (2 : ℂ) ^ (-s))⁻¹ := by
    unfold progressionSmearer
    rw [div_eq_mul_inv]
  rw [hf, hS]
  exact hg

/-! ## The poles -/

/-- The pole `s_k = log r/log 2 + 2πik/log 2`. -/
def progressionPole (r : ℝ) (k : ℤ) : ℂ :=
  ((Real.log r / Real.log 2 : ℝ) : ℂ) + ((2 * Real.pi * k / Real.log 2 : ℝ) : ℂ) * I

/-- Every pole lies strictly right of the critical line when `r > √2`. -/
theorem progressionPole_re {r : ℝ} (hr : Real.sqrt 2 < r) (k : ℤ) :
    1 / 2 < (progressionPole r k).re := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hre : (progressionPole r k).re = Real.log r / Real.log 2 := by
    simp only [progressionPole, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [hre, lt_div_iff₀ hl2]
  have hlog : Real.log (Real.sqrt 2) < Real.log r := Real.log_lt_log hs2 hr
  have hsq : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    rw [Real.log_sqrt (by norm_num)]
  linarith

theorem two_cpow_neg_eq_exp (s : ℂ) : (2 : ℂ) ^ (-s) = Complex.exp (-(Real.log 2 * s)) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num)]
  have h : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  rw [h]; ring_nf

/-- **The poles.**  `r·2^{−s_k} = 1`. -/
theorem mul_cpow_progressionPole {r : ℝ} (hr : 0 < r) (k : ℤ) :
    (r : ℂ) * (2 : ℂ) ^ (-progressionPole r k) = 1 := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hl2 : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos (by norm_num)).ne'
  rw [two_cpow_neg_eq_exp]
  have harg : -((Real.log 2 : ℂ) * progressionPole r k) =
      -(Real.log r : ℂ) + (-k : ℤ) * (2 * Real.pi * I) := by
    unfold progressionPole
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_neg,
    ← Complex.ofReal_exp, Real.exp_log hr]
  field_simp

theorem hasDerivAt_one_sub_mul_cpow (r : ℝ) (s : ℂ) :
    HasDerivAt (fun w : ℂ => 1 - (r : ℂ) * (2 : ℂ) ^ (-w))
      ((r : ℂ) * (2 : ℂ) ^ (-s) * (Real.log 2 : ℂ)) s := by
  have h1 : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (-w)) ((2 : ℂ) ^ (-s) * Complex.log 2 * (-1)) s :=
    (hasDerivAt_id s).neg.const_cpow (Or.inl (by norm_num))
  have hlog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h2 := (h1.const_mul (r : ℂ)).const_sub 1
  exact h2.congr_deriv (by rw [hlog]; ring)

theorem continuous_two_cpow_neg : Continuous fun w : ℂ => (2 : ℂ) ^ (-w) := by
  simp_rw [two_cpow_neg_eq_exp]; fun_prop

/-- **Negative residue.**  `(s − s_k)·S(s) → −c/(r log 2)` as `s → s_k`. -/
theorem tendsto_progressionSmearer_residue (c : ℝ) {r : ℝ} (hr : 0 < r) (k : ℤ) :
    Tendsto (fun s : ℂ => (s - progressionPole r k) * progressionSmearer c r s)
      (𝓝[≠] progressionPole r k) (𝓝 (-((c / (r * Real.log 2) : ℝ) : ℂ))) := by
  set s₀ := progressionPole r k
  have hl2 : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos (by norm_num)).ne'
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hone : (r : ℂ) * (2 : ℂ) ^ (-s₀) = 1 := mul_cpow_progressionPole hr k
  have hu₀ : (2 : ℂ) ^ (-s₀) = (r : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hone)
  set g : ℂ → ℂ := fun w => 1 - (r : ℂ) * (2 : ℂ) ^ (-w) with hgdef
  have hg0 : g s₀ = 0 := by
    show 1 - (r : ℂ) * (2 : ℂ) ^ (-s₀) = 0
    rw [hone, sub_self]
  have hgd := hasDerivAt_one_sub_mul_cpow r s₀
  rw [hone, one_mul] at hgd
  -- slope of g at s₀ tends to log 2
  have hslope := hasDerivAt_iff_tendsto_slope.mp hgd
  have hinv : Tendsto (fun s => (slope g s₀ s)⁻¹) (𝓝[≠] s₀) (𝓝 ((Real.log 2 : ℂ)⁻¹)) :=
    hslope.inv₀ hl2
  have hcont : Tendsto (fun s : ℂ => (2 : ℂ) ^ (-s)) (𝓝[≠] s₀) (𝓝 ((r : ℂ)⁻¹)) := by
    rw [← hu₀]
    exact (continuous_two_cpow_neg.tendsto s₀).mono_left nhdsWithin_le_nhds
  have hprod := (hcont.const_mul (-(c : ℂ))).mul hinv
  have hlim : -(c : ℂ) * (r : ℂ)⁻¹ * (Real.log 2 : ℂ)⁻¹ = -((c / (r * Real.log 2) : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s - s₀ ≠ 0 := sub_ne_zero.mpr hs
  rw [slope_def_field, hg0, sub_zero]
  unfold progressionSmearer
  simp only [hgdef]
  by_cases hgs : 1 - (r : ℂ) * (2 : ℂ) ^ (-s) = 0
  · rw [hgs]; simp
  · field_simp

/-! ## Exact mass per pole -/

/-- On the circle `z = R e^{iθ}` with `R > 1`, `∫_0^{2π} z/(z−1) dθ = 2π`. -/
theorem integral_circleMap_div_sub_one {R : ℝ} (hR : 1 < R) :
    ∫ θ in (0 : ℝ)..2 * π, circleMap 0 R θ / (circleMap 0 R θ - 1) = 2 * π := by
  have hmem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by simpa using hR
  have h := circleIntegral.integral_sub_inv_of_mem_ball hmem
  unfold circleIntegral at h
  simp only [deriv_circleMap, smul_eq_mul] at h
  have hfun : (fun θ : ℝ => circleMap 0 R θ * I * (circleMap 0 R θ - 1)⁻¹) =
      fun θ : ℝ => I * (circleMap 0 R θ / (circleMap 0 R θ - 1)) := by
    funext θ; rw [div_eq_mul_inv]; ring
  rw [hfun, intervalIntegral.integral_const_mul] at h
  have hI : I ≠ 0 := I_ne_zero
  have h' : I * (∫ θ in (0 : ℝ)..2 * π, circleMap 0 R θ / (circleMap 0 R θ - 1)) =
      I * (2 * π) := by rw [h]; ring
  exact mul_left_cancel₀ hI h'

theorem mul_two_cpow_neg_line_eq_circleMap (r t : ℝ) :
    (r : ℂ) * (2 : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) =
      circleMap 0 (r / Real.sqrt 2) (-Real.log 2 * t) := by
  rw [two_cpow_neg_eq_exp, circleMap, zero_add]
  have hsplit : -((Real.log 2 : ℂ) * ((1 / 2 : ℂ) + t * I)) =
      ((-(Real.log 2 / 2) : ℝ) : ℂ) + ((-Real.log 2 * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hsplit, Complex.exp_add, ← Complex.ofReal_exp]
  have hexp : Real.exp (-(Real.log 2 / 2)) = (Real.sqrt 2)⁻¹ := by
    rw [Real.exp_neg, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 2; ring
  rw [hexp]
  push_cast
  ring

theorem circleMap_ne_one {R : ℝ} (hR : 1 < R) (θ : ℝ) : circleMap 0 R θ ≠ 1 := by
  intro h
  have hn := congrArg norm h
  rw [norm_circleMap_zero, norm_one, abs_of_pos (by linarith)] at hn
  linarith

theorem progressionSmearer_line_eq_circle (c : ℝ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    progressionSmearer c r ((1 / 2 : ℂ) + t * I) =
      ((c / r : ℝ) : ℂ) * (circleMap 0 (r / Real.sqrt 2) (-Real.log 2 * t) /
        (circleMap 0 (r / Real.sqrt 2) (-Real.log 2 * t) - 1)) := by
  rw [progressionSmearer_eq c hr.ne', mul_two_cpow_neg_line_eq_circleMap]

/-- **Exact mass per pole.**  For `c ∈ ℝ` and `r > √2`, the integral of the progression smearer
over one period of the critical line is `(c/r)·(2π/log 2)`, i.e. `2π` times the absolute residue
`c/(r log 2)` of the single pole whose ordinate lies in the period. -/
theorem integral_progressionSmearer_period (c : ℝ) {r : ℝ} (hr : Real.sqrt 2 < r) :
    ∫ t in (0 : ℝ)..2 * π / Real.log 2, progressionSmearer c r ((1 / 2 : ℂ) + t * I) =
      ((c / r * (2 * π / Real.log 2) : ℝ) : ℂ) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hr0 : 0 < r := hs2.trans hr
  have hR : 1 < r / Real.sqrt 2 := by rw [lt_div_iff₀ hs2]; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set R := r / Real.sqrt 2
  set g : ℝ → ℂ := fun θ => circleMap 0 R θ / (circleMap 0 R θ - 1) with hg
  have hper : Function.Periodic g (2 * π) := by
    intro θ; simp only [hg, periodic_circleMap 0 R θ]
  simp_rw [progressionSmearer_line_eq_circle c hr0]
  rw [intervalIntegral.integral_const_mul]
  have hsub : ∫ t in (0 : ℝ)..2 * π / Real.log 2, g (-Real.log 2 * t) =
      (-Real.log 2)⁻¹ • ∫ u in (-Real.log 2 * 0)..(-Real.log 2 * (2 * π / Real.log 2)), g u :=
    intervalIntegral.integral_comp_mul_left g (by linarith)
  have hend : -Real.log 2 * (2 * π / Real.log 2) = -(2 * π) := by field_simp
  rw [mul_zero, hend] at hsub
  have hflip : ∫ u in (0 : ℝ)..-(2 * π), g u = -∫ u in -(2 * π)..0, g u :=
    intervalIntegral.integral_symm _ _
  have hshift : ∫ u in -(2 * π)..0, g u = ∫ u in (0 : ℝ)..2 * π, g u := by
    have := hper.intervalIntegral_add_eq (-(2 * π)) 0
    simpa using this
  have hcirc := integral_circleMap_div_sub_one hR
  simp only [hg] at hsub hshift hflip
  rw [hsub, hflip, hshift, hcirc]
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- **Exact mass per pole, real part.**  `∫_0^{2π/log 2} Re S(½ + it) dt = (c/r)·(2π/log 2)`. -/
theorem integral_re_progressionSmearer_period (c : ℝ) {r : ℝ} (hr : Real.sqrt 2 < r) :
    ∫ t in (0 : ℝ)..2 * π / Real.log 2, (progressionSmearer c r ((1 / 2 : ℂ) + t * I)).re =
      c / r * (2 * π / Real.log 2) := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hr0 : 0 < r := hs2.trans hr
  have hR : 1 < r / Real.sqrt 2 := by rw [lt_div_iff₀ hs2]; linarith
  have hcont : Continuous fun t : ℝ => progressionSmearer c r ((1 / 2 : ℂ) + t * I) := by
    simp_rw [progressionSmearer_line_eq_circle c hr0]
    refine continuous_const.mul (Continuous.div ?_ ?_ fun t => sub_ne_zero.mpr
      (circleMap_ne_one hR _))
    · exact (continuous_circleMap 0 _).comp (continuous_const.mul continuous_id)
    · exact ((continuous_circleMap 0 _).comp (continuous_const.mul continuous_id)).sub
        continuous_const
  have h := Complex.reCLM.intervalIntegral_comp_comm
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * π / Real.log 2))
  simp only [Complex.reCLM_apply] at h
  rw [h, integral_progressionSmearer_period c hr, Complex.ofReal_re]

end RHTower.PeriodicSmearing
