import GaloisForLFunctions.RHTower.PrimeBlindNonnegativeConeReduction
import GaloisForLFunctions.RHTower.DigammaQuarter

/-!
# Gauss-mode pole cancellation and closed-form antiderivative for the Lévy–pole Weil functional

For a real test `f ∈ C²_c(ℝ)` and its autocorrelation `k = f ⋆ f̃`, `WeilArchReLevyPoleForm` writes
the pole and archimedean part of the Weil functional as

`W_∞(k) = A(0) ‖f‖₂² + ∫_0^∞ ω(x) ‖f − f(· + x)‖₂² dx + 2 ∫∫ f(u) f(v) cosh((u − v)/2) du dv`,

where `A(0) = EF.gammaBracket 0 = ψ(1/4) − log π < 0` and `ω(x) = e^{−x/2}/(1 − e^{−2x})`
(`archLevyDensity`).

This module establishes three unconditional producer ingredients for the Lévy–pole functional:

1. **Closed-form evaluation and rational sandwich for `A(0)`**
   (`gammaBracket_zero_eq_neg_archRatioCharge`, `neg_gammaBracket_zero_lt`,
   `lt_neg_gammaBracket_zero`):
   `-A(0) = log π + 3 log 2 + γ + π/2 ∈ (51/10, 28/5)`.

2. **One-mode and two-mode Gauss–pole cancellation laws**
   (`oneMode_gauss_pole_le_weilArchRe`, `twoMode_gauss_pole_le_weilArchRe`):
   Expanding `ω(x) = e^{−x/2} + e^{−5x/2} + e^{−4x} ω(x)` on `(0, ∞)` and combining the first two
   Gauss modes (`∫_0^∞ e^{−x/2} dx = 2`, `∫_0^∞ e^{−5x/2} dx = 2/5`) with the pole kernel
   `2 cosh(r/2) = e^{r/2} + e^{−r/2}` cancels the decaying exponential `e^{−|u−v|/2}` identically:
   * *One-mode law (valid for all signed `f ∈ C²_c(ℝ)`):*
     `(A(0) + 4) ∫ f² + ∫∫ f(u) f(v) e^{|u−v|/2} du dv ≤ W_∞(f ⋆ f̃)`.
     For `f ≥ 0`, `e^{|u−v|/2} ≥ 1` yields `(A(0) + 4) ‖f‖₂² + ‖f‖₁² ≤ W_∞(f ⋆ f̃)`
     (`l1_sq_add_oneMode_le_weilArchRe`), so any nonnegative test with
     `‖f‖₁² ≥ (−A(0) − 4) ‖f‖₂²` (in particular `‖f‖₁² ≥ (8/5) ‖f‖₂²`) has `W_∞(f ⋆ f̃) ≥ 0`
     unconditionally (`weilArchRe_nonneg_of_l1_sq_ge`).
   * *Two-mode law (valid for all signed `f ∈ C²_c(ℝ)`):*
     `(A(0) + 24/5) ∫ f² + ∫∫ f(u) f(v) (e^{|u−v|/2} − e^{−5|u−v|/2}) du dv ≤ W_∞(f ⋆ f̃)`.
     Since `e^{r/2} − e^{−5r/2} = 2 e^{−r} sinh(3r/2) ≥ 0` on `[0, ∞)`, every nonnegative test
     satisfies `(A(0) + 24/5) ‖f‖₂² ≤ W_∞(f ⋆ f̃)` (`twoMode_floor_le_weilArchRe`), improving the
     anomaly bound of `WeilBlindPoleSignLaw` by `+24/5 = +4.8` without any support or blindness
     hypothesis.

3. **Exact closed-form antiderivative of `ω` and unconditional short-support positivity**
   (`hasDerivAt_archLevyAntideriv`, `integral_archLevyDensity_Icc`,
   `weilEnergyNonneg_of_volume_pos_le`, `weilArchRe_nonneg_of_volume_pos_le_inv_128`):
   The function
   `Ω(y) = (1/2) (log(1 + e^{−y/2}) − log(1 − e^{−y/2})) + arctan(e^{−y/2})`
   satisfies `Ω'(y) = −ω(y)` on `(0, ∞)`. For any nonnegative `g` whose positivity set
   `S = {x | 0 < g x}` has measure `|S| ≤ L`, quantile rearrangement onto `(0, |S|) ⊆ (0, L)`
   makes `g*` disjoint from `g*(· + x)` for all `x ≥ L`, giving `jumpEnergy g ≥ 2 Ω(L) ‖g‖₂²`.
   Whenever `2 Ω(L) ≥ −A(0)` (in particular for all `L ≤ 1/128`), `WeilEnergyNonneg g` and
   `0 ≤ W_∞(f ⋆ f̃)` hold unconditionally without `WindowPositive`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry.QuantileTransport

namespace RHTower.WeilLevyPoleGauss

noncomputable section

open WeilLevyPole RHTower.NonnegativeCone

/-! ## Section 1: Closed-form evaluation and rational sandwich for `EF.gammaBracket 0` -/

/-- `EF.gammaBracket 0` is the negative of `archRatioCharge = log π + 3 log 2 + γ + π/2`. -/
theorem gammaBracket_zero_eq_neg_archRatioCharge :
    EF.gammaBracket 0 = -GaloisForLFunctions.RHTower.archRatioCharge := by
  unfold EF.gammaBracket GaloisForLFunctions.RHTower.archRatioCharge
  have h0 : (1 / 4 + Complex.I * (0 : ℝ) / 2 : ℂ) = (1 / 4 : ℂ) := by push_cast; ring
  rw [h0, GaloisForLFunctions.RHTower.digamma_quarter, Complex.neg_re, Complex.ofReal_re]
  ring

/-- Explicit closed form for `-EF.gammaBracket 0`. -/
theorem neg_gammaBracket_zero_eq :
    -EF.gammaBracket 0 =
      Real.log Real.pi + 3 * Real.log 2 + Real.eulerMascheroniConstant + Real.pi / 2 := by
  rw [gammaBracket_zero_eq_neg_archRatioCharge, neg_neg,
    GaloisForLFunctions.RHTower.archRatioCharge]

/-- The origin value `EF.gammaBracket 0` is strictly negative. -/
theorem gammaBracket_zero_lt_zero : EF.gammaBracket 0 < 0 := by
  rw [gammaBracket_zero_eq_neg_archRatioCharge]
  exact neg_lt_zero.mpr GaloisForLFunctions.RHTower.archRatioCharge_pos

/-- Elementary upper bound `log π ≤ log 2 + π/2 − 1` from `π = 2 · (π/2)` and `log x ≤ x − 1`. -/
theorem log_pi_le : Real.log Real.pi ≤ Real.log 2 + Real.pi / 2 - 1 := by
  have hpi : Real.pi = 2 * (Real.pi / 2) := by ring
  have hpos : 0 < Real.pi / 2 := by positivity
  have h1 : Real.log Real.pi = Real.log 2 + Real.log (Real.pi / 2) := by
    conv_lhs => rw [hpi]
    exact Real.log_mul two_ne_zero hpos.ne'
  have h2 : Real.log (Real.pi / 2) ≤ Real.pi / 2 - 1 := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Elementary lower bound `1 < log π`. -/
theorem one_lt_log_pi : 1 < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 := Real.exp_one_lt_d9
  have h2 := Real.pi_gt_d4
  linarith

/-- **Unconditional rational upper bound**: `-EF.gammaBracket 0 < 28 / 5` (`= 5.6`). -/
theorem neg_gammaBracket_zero_lt : -EF.gammaBracket 0 < 28 / 5 := by
  rw [neg_gammaBracket_zero_eq]
  have h1 := log_pi_le
  have h2 := Real.log_two_lt_d9
  have h3 := Real.eulerMascheroniConstant_lt_two_thirds
  have h4 := Real.pi_lt_d4
  linarith

/-- **Unconditional rational lower bound**: `51 / 10 < -EF.gammaBracket 0` (`= 5.1`). -/
theorem lt_neg_gammaBracket_zero : 51 / 10 < -EF.gammaBracket 0 := by
  rw [neg_gammaBracket_zero_eq]
  have h1 := one_lt_log_pi
  have h2 := Real.log_two_gt_d9
  have h3 := Real.one_half_lt_eulerMascheroniConstant
  have h4 := Real.pi_gt_d4
  linarith

/-! ## Section 2: One-mode and two-mode Gauss decompositions of `archLevyDensity` -/

/-- One-mode Gauss decomposition: `ω(x) = e^{−x/2} + e^{−2x} ω(x)` for `x ≠ 0`. -/
theorem archLevyDensity_eq_oneMode {x : ℝ} (hx : x ≠ 0) :
    archLevyDensity x = Real.exp (-x / 2) + Real.exp (-2 * x) * archLevyDensity x := by
  have hden : 1 - Real.exp (-2 * x) ≠ 0 := by
    intro h
    have h1 : Real.exp (-2 * x) = Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact hx (by linarith [Real.exp_injective h1])
  calc archLevyDensity x
      = (Real.exp (-x / 2) * (1 - Real.exp (-2 * x)) +
          Real.exp (-2 * x) * Real.exp (-x / 2)) / (1 - Real.exp (-2 * x)) := by
        unfold archLevyDensity; congr 1; ring
    _ = Real.exp (-x / 2) + Real.exp (-2 * x) * archLevyDensity x := by
        unfold archLevyDensity
        rw [add_div, mul_div_cancel_right₀ _ hden, mul_div_assoc]

/-- Two-mode Gauss decomposition:
`ω(x) = e^{−x/2} + e^{−5x/2} + e^{−4x} ω(x)` for `x ≠ 0`. -/
theorem archLevyDensity_eq_twoMode {x : ℝ} (hx : x ≠ 0) :
    archLevyDensity x =
      Real.exp (-x / 2) + Real.exp (-5 * x / 2) + Real.exp (-4 * x) * archLevyDensity x := by
  have h1 := archLevyDensity_eq_oneMode hx
  have hexp : Real.exp (-2 * x) * Real.exp (-x / 2) = Real.exp (-5 * x / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hexp2 : Real.exp (-2 * x) ^ 2 = Real.exp (-4 * x) := by
    rw [sq, ← Real.exp_add]; ring_nf
  linear_combination (1 + Real.exp (-2 * x)) * h1 + hexp + archLevyDensity x * hexp2

/-- The Lévy density dominates its `k = 0` Gauss mode `e^{−x/2}` on `(0, ∞)`. -/
theorem archLevyDensity_ge_oneMode {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) ≤ archLevyDensity x := by
  rw [archLevyDensity_eq_oneMode hx.ne']
  have hpos : 0 ≤ Real.exp (-2 * x) * archLevyDensity x :=
    mul_nonneg (Real.exp_pos _).le (archLevyDensity_pos hx).le
  linarith

/-- The Lévy density dominates its first two Gauss modes `e^{−x/2} + e^{−5x/2}` on `(0, ∞)`. -/
theorem archLevyDensity_ge_twoMode {x : ℝ} (hx : 0 < x) :
    Real.exp (-x / 2) + Real.exp (-5 * x / 2) ≤ archLevyDensity x := by
  rw [archLevyDensity_eq_twoMode hx.ne']
  have hpos : 0 ≤ Real.exp (-4 * x) * archLevyDensity x :=
    mul_nonneg (Real.exp_pos _).le (archLevyDensity_pos hx).le
  linarith

/-- **One-mode pole cancellation**: `2 cosh(r/2) − e^{−r/2} = e^{r/2}`. -/
theorem two_mul_cosh_sub_exp_neg_half (r : ℝ) :
    2 * Real.cosh (r / 2) - Real.exp (-r / 2) = Real.exp (r / 2) := by
  rw [Real.cosh_eq, show -(r / 2) = -r / 2 by ring]
  ring

/-- **Two-mode pole cancellation**:
`2 cosh(r/2) − (e^{−r/2} + e^{−5r/2}) = e^{r/2} − e^{−5r/2}`. -/
theorem two_mul_cosh_sub_twoMode (r : ℝ) :
    2 * Real.cosh (r / 2) - (Real.exp (-r / 2) + Real.exp (-5 * r / 2)) =
      Real.exp (r / 2) - Real.exp (-5 * r / 2) := by
  rw [Real.cosh_eq, show -(r / 2) = -r / 2 by ring]
  ring

/-- Hyperbolic factorization of the two-mode residual pole kernel:
`e^{r/2} − e^{−5r/2} = 2 e^{−r} sinh(3r/2)`. -/
theorem exp_half_sub_exp_neg_five_half_eq_sinh (r : ℝ) :
    Real.exp (r / 2) - Real.exp (-5 * r / 2) = 2 * Real.exp (-r) * Real.sinh (3 * r / 2) := by
  rw [Real.sinh_eq]
  have h1 : Real.exp (-r) * Real.exp (3 * r / 2) = Real.exp (r / 2) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-r) * Real.exp (-(3 * r / 2)) = Real.exp (-5 * r / 2) := by
    rw [← Real.exp_add]; ring_nf
  linear_combination -h1 + h2

/-- The two-mode residual pole kernel `e^{r/2} − e^{−5r/2}` is nonnegative for `r ≥ 0`. -/
theorem exp_half_sub_exp_neg_five_half_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ Real.exp (r / 2) - Real.exp (-5 * r / 2) := by
  have : -5 * r / 2 ≤ r / 2 := by linarith
  linarith [Real.exp_le_exp.mpr this]

/-! ## Section 3: Exponential jump energy identity and Gauss–pole cancellation laws -/

/-- For any bounded finite-support measurable `h` and rate `α > 0`,
`∫_{x>0} e^{−αx} ∫ (h(u) − h(u+x))² du dx = (2/α) ∫ h² − ∫∫ h(u) h(v) e^{−α|u−v|} du dv`. -/
theorem integral_exp_mul_jump_sq {A : Set ℝ} {h : ℝ → ℝ} {C α : ℝ}
    (hh : BddSupp A h C) (hα : 0 < α) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-α * x) * (∫ u, (h u - h (u + x)) ^ 2) =
      (2 / α) * (∫ u, h u ^ 2) -
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-α * |p.1 - p.2|) := by
  set k : ℝ → ℝ := fun r => Real.exp (-α * |r|) with hkdef
  have hk_meas : Measurable k := by unfold k; fun_prop
  have hk_bound : ∀ r, |k r| ≤ 1 := fun r => by
    unfold k
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg r])
  have hpair := integral_pair_eq_two_mul_Ioi hh hk_meas hk_bound
  have hpair_eq : (∫ p : ℝ × ℝ, h p.1 * h p.2 * k |p.1 - p.2|) =
      ∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-α * |p.1 - p.2|) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp [hkdef, abs_abs]
  rw [hpair_eq] at hpair
  have hI_exp : IntegrableOn (fun x : ℝ => Real.exp (-α * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hI_auto : IntegrableOn (fun x : ℝ => Real.exp (-α * x) * autocorr h x) (Ioi 0) := by
    refine (integrable_kernel_mul_autocorr hh hk_meas hk_bound).integrableOn.congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [hkdef, abs_of_pos (mem_Ioi.mp hx)]
  have hcongr : EqOn (fun x : ℝ => Real.exp (-α * x) * ∫ u, (h u - h (u + x)) ^ 2)
      (fun x : ℝ => 2 * (∫ u, h u ^ 2) * Real.exp (-α * x) -
        2 * (Real.exp (-α * x) * autocorr h x)) (Ioi 0) := fun x _ => by
    simp only
    rw [integral_jump_sq hh x]
    ring
  have hcongr_k : (∫ x in Ioi (0 : ℝ), k x * autocorr h x) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-α * x) * autocorr h x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      simp [hkdef, abs_of_pos (mem_Ioi.mp hx)]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_sub (hI_exp.const_mul _) (hI_auto.const_mul 2),
    integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -α < 0) 0, hpair, hcongr_k]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- The `L¹ × L¹` pair integral against `e^{−α|u−v|}` is integrable for `BddSupp A h C`. -/
theorem integrable_pair_exp_neg {A : Set ℝ} {h : ℝ → ℝ} {C α : ℝ}
    (hh : BddSupp A h C) (hα : 0 ≤ α) :
    Integrable (fun p : ℝ × ℝ => h p.1 * h p.2 * Real.exp (-α * |p.1 - p.2|)) := by
  rw [Measure.volume_eq_prod]
  refine ((hh.integrable.abs.mul_prod hh.integrable.abs).mul_const (1 : ℝ)).mono'
    (((hh.meas.comp measurable_fst).mul (hh.meas.comp measurable_snd)).mul
      (by fun_prop : Measurable fun p : ℝ × ℝ =>
        Real.exp (-α * |p.1 - p.2|))).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-α * |p.1 - p.2|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (p.1 - p.2)])
  exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- One-mode Gauss lower bound on `jumpEnergy h` in `ENNReal`. -/
theorem ofReal_oneMode_le_jumpEnergy {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) :
    ENNReal.ofReal (4 * (∫ u, h u ^ 2) -
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) ≤
      jumpEnergy h := by
  have h1 := integral_exp_mul_jump_sq hh (α := 1 / 2) (by norm_num)
  rw [show (2 / (1 / 2) : ℝ) = 4 by norm_num] at h1
  rw [← h1]
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hDm := measurable_jump hh
  have hI : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2)
      (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).mul_const
      (4 * ∫ u, h u ^ 2)).mono'
      ((by fun_prop : Measurable fun x : ℝ => Real.exp (-(1 / 2) * x)).mul hDm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) (Real.exp_pos _).le
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun x => mul_nonneg (Real.exp_pos _).le (hD0 x))]
  unfold jumpEnergy
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
  rw [show -(1 / 2 : ℝ) * x = -x / 2 by ring]
  exact mul_le_mul_of_nonneg_right (archLevyDensity_ge_oneMode hx) (hD0 x)

/-- Two-mode Gauss lower bound on `jumpEnergy h` in `ENNReal`. -/
theorem ofReal_twoMode_le_jumpEnergy {A : Set ℝ} {h : ℝ → ℝ} {C : ℝ} (hh : BddSupp A h C) :
    ENNReal.ofReal ((24 / 5) * (∫ u, h u ^ 2) -
        ((∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
          ∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|))) ≤
      jumpEnergy h := by
  have h1 := integral_exp_mul_jump_sq hh (α := 1 / 2) (by norm_num)
  have h2 := integral_exp_mul_jump_sq hh (α := 5 / 2) (by norm_num)
  have hD0 : ∀ x, 0 ≤ ∫ u, (h u - h (u + x)) ^ 2 := fun x => integral_nonneg fun _ => sq_nonneg _
  have hDm := measurable_jump hh
  have hI1 : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2)
      (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 0).mul_const
      (4 * ∫ u, h u ^ 2)).mono'
      ((by fun_prop : Measurable fun x : ℝ => Real.exp (-(1 / 2) * x)).mul hDm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) (Real.exp_pos _).le
  have hI2 : IntegrableOn (fun x : ℝ => Real.exp (-(5 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2)
      (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (by norm_num : -(5 / 2 : ℝ) < 0) 0).mul_const
      (4 * ∫ u, h u ^ 2)).mono'
      ((by fun_prop : Measurable fun x : ℝ => Real.exp (-(5 / 2) * x)).mul hDm).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hD0 x))]
    exact mul_le_mul_of_nonneg_left (jump_le hh x) (Real.exp_pos _).le
  have hsum : (24 / 5) * (∫ u, h u ^ 2) -
      ((∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
        ∫ p : ℝ × ℝ, h p.1 * h p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) =
      ∫ x in Ioi (0 : ℝ), (Real.exp (-(1 / 2) * x) + Real.exp (-(5 / 2) * x)) *
        ∫ u, (h u - h (u + x)) ^ 2 := by
    have hadd : (∫ x in Ioi (0 : ℝ), (Real.exp (-(1 / 2) * x) + Real.exp (-(5 / 2) * x)) *
        ∫ u, (h u - h (u + x)) ^ 2) =
        (∫ x in Ioi (0 : ℝ), Real.exp (-(1 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2) +
          ∫ x in Ioi (0 : ℝ), Real.exp (-(5 / 2) * x) * ∫ u, (h u - h (u + x)) ^ 2 := by
      rw [← integral_add hI1 hI2]
      exact setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
    rw [hadd, h1, h2]
    ring
  rw [hsum, ofReal_integral_eq_lintegral_ofReal
    ((hI1.add hI2).congr_fun (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi)
    (ae_of_all _ fun x => mul_nonneg (by positivity) (hD0 x))]
  unfold jumpEnergy
  refine setLIntegral_mono' measurableSet_Ioi fun x hx => ENNReal.ofReal_le_ofReal ?_
  rw [show -(1 / 2 : ℝ) * x = -x / 2 by ring, show -(5 / 2 : ℝ) * x = -5 * x / 2 by ring]
  exact mul_le_mul_of_nonneg_right (archLevyDensity_ge_twoMode hx) (hD0 x)

/-- Every continuous compactly supported `f : ℝ → ℝ` satisfies `BddSupp` on some `Icc (-R) R`. -/
theorem exists_bddSupp_of_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    ∃ R C : ℝ, BddSupp (Icc (-R) R) f C := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC⟩ := hf.abs.bddAbove_range_of_hasCompactSupport hfc.abs
  refine ⟨R, C, hf.measurable, fun x => hC ⟨x, rfl⟩, fun x hx => ?_, measurableSet_Icc, ?_⟩
  · by_contra hne
    apply hx
    have hmem := hR (subset_tsupport f hne)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hmem
    exact abs_le.mp hmem
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

private theorem le_toReal_of_ofReal_le {a : ℝ} {b : ENNReal} (hb : b ≠ ⊤)
    (h : ENNReal.ofReal a ≤ b) : a ≤ b.toReal := by
  have h1 := ENNReal.toReal_mono hb h
  rcases le_or_gt 0 a with ha | ha
  · rwa [ENNReal.toReal_ofReal ha] at h1
  · exact ha.le.trans ENNReal.toReal_nonneg

/-- **One-mode Gauss–pole lower bound for `weilArchRe` (all signed `f ∈ C²_c(ℝ)`).**
For every real `C²` compactly supported test `f`,
`(A(0) + 4) ∫ f² + ∫∫ f(u) f(v) e^{|u−v|/2} du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem oneMode_gauss_pole_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 4) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2)) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h1' : 4 * (∫ u, f u ^ 2) -
      (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) ≤
      (jumpEnergy f).toReal :=
    le_toReal_of_ofReal_le hJ (ofReal_oneMode_le_jumpEnergy hB)
  have hcs_cosh : HasCompactSupport fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1 | h2
    · rw [image_eq_zero_of_notMem_tsupport h1]; ring
    · rw [image_eq_zero_of_notMem_tsupport h2]; ring
  have hI_cosh : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)).integrable_of_hasCompactSupport hcs_cosh
  have hI_neg : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hcomb : 2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
      (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) =
      ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2) := by
    rw [← integral_const_mul, ← integral_sub (hI_cosh.const_mul 2) hI_neg]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only
    have hca : Real.cosh ((p.1 - p.2) / 2) = Real.cosh (|p.1 - p.2| / 2) := by
      rw [← Real.cosh_abs, abs_div, abs_two]
    have hlin := two_mul_cosh_sub_exp_neg_half |p.1 - p.2|
    rw [hca, show -(1 / 2 : ℝ) * |p.1 - p.2| = -|p.1 - p.2| / 2 by ring]
    linear_combination f p.1 * f p.2 * hlin
  rw [weilArchRe_eq_levy_pole hf hfc]
  change _ ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + (jumpEnergy f).toReal +
    2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  linarith

/-- **One-mode `L¹`–`L²` lower bound on the nonnegative cone**:
for every nonnegative `f ∈ C²_c(ℝ)`,
`(A(0) + 4) ∫ f² + (∫ f)² ≤ W_∞(f ⋆ f̃)`. -/
theorem l1_sq_add_oneMode_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) :
    (EF.gammaBracket 0 + 4) * (∫ u, f u ^ 2) + (∫ u, f u) ^ 2 ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := oneMode_gauss_pole_le_weilArchRe hf hfc
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hcs : HasCompactSupport fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1 | h2
    · rw [image_eq_zero_of_notMem_tsupport h1]; ring
    · rw [image_eq_zero_of_notMem_tsupport h2]; ring
  have hI_exp : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2)).integrable_of_hasCompactSupport hcs
  have hI_prod : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 := by
    rw [Measure.volume_eq_prod]
    exact hfi.mul_prod hfi
  have hsq : (∫ u, f u) ^ 2 = ∫ p : ℝ × ℝ, f p.1 * f p.2 := by
    rw [sq, Measure.volume_eq_prod, integral_prod_mul]
  have hmono : (∫ p : ℝ × ℝ, f p.1 * f p.2) ≤
      ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (|p.1 - p.2| / 2) := by
    refine integral_mono hI_prod hI_exp fun p => ?_
    have hfp : 0 ≤ f p.1 * f p.2 := mul_nonneg (hf0 _) (hf0 _)
    have hexp : 1 ≤ Real.exp (|p.1 - p.2| / 2) := Real.one_le_exp (by positivity)
    exact le_mul_of_one_le_right hfp hexp
  linarith

/-- **Unconditional positivity for flat nonnegative tests**: if `f ≥ 0` satisfies
`(-A(0) - 4) ∫ f² ≤ (∫ f)²` (in particular whenever `(8/5) ∫ f² ≤ (∫ f)²`), then
`0 ≤ W_∞(f ⋆ f̃)`. -/
theorem weilArchRe_nonneg_of_l1_sq_ge {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hflat : (-EF.gammaBracket 0 - 4) * (∫ u, f u ^ 2) ≤ (∫ u, f u) ^ 2) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have h := l1_sq_add_oneMode_le_weilArchRe hf hfc hf0
  linarith

/-- Rational-threshold specialization: any nonnegative `f ∈ C²_c(ℝ)` with `(8/5) ∫ f² ≤ (∫ f)²`
has `0 ≤ W_∞(f ⋆ f̃)` unconditionally. -/
theorem weilArchRe_nonneg_of_eight_fifths_l2_le_l1_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u)
    (hflat : (8 / 5) * (∫ u, f u ^ 2) ≤ (∫ u, f u) ^ 2) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  refine weilArchRe_nonneg_of_l1_sq_ge hf hfc hf0 ?_
  have hA := neg_gammaBracket_zero_lt
  have hsq : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  nlinarith

/-- **Two-mode Gauss–pole lower bound for `weilArchRe` (all signed `f ∈ C²_c(ℝ)`).**
For every real `C²` compactly supported test `f`,
`(A(0) + 24/5) ∫ f² + ∫∫ f(u) f(v) (e^{|u−v|/2} − e^{−5|u−v|/2}) du dv ≤ W_∞(f ⋆ f̃)`. -/
theorem twoMode_gauss_pole_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    (EF.gammaBracket 0 + 24 / 5) * (∫ u, f u ^ 2) +
        (∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (Real.exp (|p.1 - p.2| / 2) - Real.exp (-5 * |p.1 - p.2| / 2))) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  obtain ⟨R, C, hB⟩ := exists_bddSupp_of_hasCompactSupport hf.continuous hfc
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  have h2' : (24 / 5) * (∫ u, f u ^ 2) -
      ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
        ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) ≤
      (jumpEnergy f).toReal :=
    le_toReal_of_ofReal_le hJ (ofReal_twoMode_le_jumpEnergy hB)
  have hcs_cosh : HasCompactSupport fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) := by
    refine HasCompactSupport.intro (hfc.isCompact.prod hfc.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport f ∧ p.2 ∈ tsupport f) from hp) with h1 | h2
    · rw [image_eq_zero_of_notMem_tsupport h1]; ring
    · rw [image_eq_zero_of_notMem_tsupport h2]; ring
  have hI_cosh : Integrable fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)).integrable_of_hasCompactSupport hcs_cosh
  have hI_1 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hI_5 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|) :=
    integrable_pair_exp_neg hB (by norm_num)
  have hI_15 : Integrable fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|) +
        f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|) := hI_1.add hI_5
  have hcomb : 2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
      ((∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(1 / 2) * |p.1 - p.2|)) +
        ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.exp (-(5 / 2) * |p.1 - p.2|)) =
      ∫ p : ℝ × ℝ, f p.1 * f p.2 *
        (Real.exp (|p.1 - p.2| / 2) - Real.exp (-5 * |p.1 - p.2| / 2)) := by
    rw [← integral_add hI_1 hI_5, ← integral_const_mul,
      ← integral_sub (hI_cosh.const_mul 2) hI_15]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only
    have hca : Real.cosh ((p.1 - p.2) / 2) = Real.cosh (|p.1 - p.2| / 2) := by
      rw [← Real.cosh_abs, abs_div, abs_two]
    have hlin := two_mul_cosh_sub_twoMode |p.1 - p.2|
    rw [hca, show -(1 / 2 : ℝ) * |p.1 - p.2| = -|p.1 - p.2| / 2 by ring,
      show -(5 / 2 : ℝ) * |p.1 - p.2| = -5 * |p.1 - p.2| / 2 by ring]
    linear_combination f p.1 * f p.2 * hlin
  rw [weilArchRe_eq_levy_pole hf hfc]
  change _ ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + (jumpEnergy f).toReal +
    2 * ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  linarith

/-- **Universal two-mode floor on the nonnegative cone**:
every nonnegative `f ∈ C²_c(ℝ)` satisfies `(A(0) + 24/5) ∫ f² ≤ W_∞(f ⋆ f̃)`. -/
theorem twoMode_floor_le_weilArchRe {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ u, 0 ≤ f u) :
    (EF.gammaBracket 0 + 24 / 5) * (∫ u, f u ^ 2) ≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hmain := twoMode_gauss_pole_le_weilArchRe hf hfc
  have hpair_nn : 0 ≤ ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (Real.exp (|p.1 - p.2| / 2) - Real.exp (-5 * |p.1 - p.2| / 2)) :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _))
      (exp_half_sub_exp_neg_five_half_nonneg (abs_nonneg _))
  linarith

/-! ## Section 4: Closed-form antiderivative of `archLevyDensity` and short-support positivity -/

/-- `archLevyDensity` is continuous on `(0, ∞)`. -/
theorem continuousOn_archLevyDensity : ContinuousOn archLevyDensity (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have h2 : 1 - Real.exp (-2 * x) ≠ 0 := by
    have : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hc : ContinuousAt (fun x : ℝ => Real.exp (-x / 2) / (1 - Real.exp (-2 * x))) x :=
    ContinuousAt.div (f := fun x : ℝ => Real.exp (-x / 2))
      (g := fun x : ℝ => 1 - Real.exp (-2 * x)) (by fun_prop) (by fun_prop) h2
  exact hc.continuousWithinAt

/-- Exact elementary antiderivative of `-archLevyDensity` on `(0, ∞)`:
`Ω(y) = (1/2) (log(1 + e^{−y/2}) − log(1 − e^{−y/2})) + arctan(e^{−y/2})`. -/
def archLevyAntideriv (y : ℝ) : ℝ :=
  (1 / 2) * (Real.log (1 + Real.exp (-y / 2)) - Real.log (1 - Real.exp (-y / 2))) +
    Real.arctan (Real.exp (-y / 2))

/-- On `(0, ∞)`, `archLevyAntideriv y` equals
`(1/2) log((1 + e^{−y/2}) / (1 − e^{−y/2})) + arctan(e^{−y/2})`. -/
theorem archLevyAntideriv_eq_log_div {y : ℝ} (hy : 0 < y) :
    archLevyAntideriv y =
      (1 / 2) * Real.log ((1 + Real.exp (-y / 2)) / (1 - Real.exp (-y / 2))) +
        Real.arctan (Real.exp (-y / 2)) := by
  unfold archLevyAntideriv
  have h1 : 0 < 1 + Real.exp (-y / 2) := by positivity
  have h2 : 0 < 1 - Real.exp (-y / 2) := by
    have : Real.exp (-y / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [Real.log_div h1.ne' h2.ne']

/-- `archLevyAntideriv y` is strictly positive for `y > 0`. -/
theorem archLevyAntideriv_pos {y : ℝ} (hy : 0 < y) : 0 < archLevyAntideriv y := by
  rw [archLevyAntideriv_eq_log_div hy]
  have ht0 : 0 < Real.exp (-y / 2) := Real.exp_pos _
  have ht1 : Real.exp (-y / 2) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlog : 0 < Real.log ((1 + Real.exp (-y / 2)) / (1 - Real.exp (-y / 2))) :=
    Real.log_pos ((one_lt_div (by linarith)).mpr (by linarith))
  have harc : 0 < Real.arctan (Real.exp (-y / 2)) := Real.arctan_pos.mpr ht0
  linarith

/-- **Exact derivative**: `Ω'(y) = −ω(y)` for every `y > 0`. -/
theorem hasDerivAt_archLevyAntideriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt archLevyAntideriv (-archLevyDensity y) y := by
  set t : ℝ := Real.exp (-y / 2) with htdef
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1t : 0 < 1 + t := by linarith
  have h1mt : 0 < 1 - t := by linarith
  have hlin : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2) y := by
    simpa [neg_div] using (hasDerivAt_id y).neg.div_const 2
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-u / 2)) (t * (-1 / 2)) y :=
    hlin.exp
  have hlog1 : HasDerivAt (fun u : ℝ => Real.log (1 + Real.exp (-u / 2)))
      (t * (-1 / 2) / (1 + t)) y :=
    (hexp.const_add 1).log h1t.ne'
  have hlog2 : HasDerivAt (fun u : ℝ => Real.log (1 - Real.exp (-u / 2)))
      (-(t * (-1 / 2)) / (1 - t)) y :=
    (hexp.const_sub 1).log h1mt.ne'
  have harc : HasDerivAt (fun u => Real.arctan (Real.exp (-u / 2)))
      (1 / (1 + t ^ 2) * (t * (-1 / 2))) y :=
    HasDerivAt.comp (h := fun u : ℝ => Real.exp (-u / 2)) y (Real.hasDerivAt_arctan t) hexp
  have hcomb : HasDerivAt archLevyAntideriv
      ((1 / 2 : ℝ) * (t * (-1 / 2) / (1 + t) - -(t * (-1 / 2)) / (1 - t)) +
        1 / (1 + t ^ 2) * (t * (-1 / 2))) y :=
    ((hlog1.sub hlog2).const_mul (1 / 2 : ℝ)).add harc
  refine hcomb.congr_deriv ?_
  have ht4 : Real.exp (-2 * y) = t ^ 4 := by
    rw [htdef, ← Real.exp_nat_mul]
    congr 1
    ring
  have hω : archLevyDensity y = t / (1 - t ^ 4) := by
    unfold archLevyDensity
    rw [← htdef, ht4]
  rw [hω]
  have hd1 : 1 + t ≠ 0 := h1t.ne'
  have hd2 : 1 - t ≠ 0 := h1mt.ne'
  have hd3 : 1 + t ^ 2 ≠ 0 := by positivity
  have hd4 : 1 - t ^ 4 ≠ 0 := by
    have hfac : 1 - t ^ 4 = (1 - t) * (1 + t) * (1 + t ^ 2) := by ring
    rw [hfac]
    positivity
  field_simp
  ring

/-- `Ω` is antitone on `(0, ∞)`. -/
theorem antitoneOn_archLevyAntideriv : AntitoneOn archLevyAntideriv (Ioi 0) := by
  intro a ha b hb hab
  have hcont : ContinuousOn (fun y => -archLevyDensity y) (uIcc a b) := by
    refine (continuousOn_archLevyDensity.mono fun y hy => ?_).neg
    rw [uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha hy.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := archLevyAntideriv) (f' := fun y => -archLevyDensity y) (a := a) (b := b)
    (fun y hy => hasDerivAt_archLevyAntideriv (by
      rw [uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1))
    hcont.intervalIntegrable
  have hneg : ∫ y in a..b, -archLevyDensity y ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_nonpos measurableSet_Ioc fun y hy =>
      neg_nonpos.mpr (archLevyDensity_pos (lt_trans ha hy.1)).le
  linarith

/-- **Exact interval integral of `archLevyDensity`**:
for `0 < a ≤ b`, `∫_a^b ω(x) dx = Ω(a) − Ω(b)`. -/
theorem integral_archLevyDensity_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, archLevyDensity x = archLevyAntideriv a - archLevyAntideriv b := by
  have hcont : ContinuousOn (fun y => -archLevyDensity y) (uIcc a b) := by
    refine (continuousOn_archLevyDensity.mono fun y hy => ?_).neg
    rw [uIcc_of_le hab] at hy
    exact lt_of_lt_of_le ha hy.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := archLevyAntideriv) (f' := fun y => -archLevyDensity y) (a := a) (b := b)
    (fun y hy => hasDerivAt_archLevyAntideriv (by
      rw [uIcc_of_le hab] at hy; exact lt_of_lt_of_le ha hy.1))
    hcont.intervalIntegrable
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

/-- Upper bound `archLevyAntideriv b ≤ 2 e^{−b/2} / (1 − e^{−b/2})` for `b > 0`. -/
theorem archLevyAntideriv_le {b : ℝ} (hb : 0 < b) :
    archLevyAntideriv b ≤ 2 * Real.exp (-b / 2) / (1 - Real.exp (-b / 2)) := by
  rw [archLevyAntideriv_eq_log_div hb]
  set t : ℝ := Real.exp (-b / 2) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h1mt : 0 < 1 - t := by linarith
  have hlog : Real.log ((1 + t) / (1 - t)) ≤ 2 * t / (1 - t) := by
    calc Real.log ((1 + t) / (1 - t)) ≤ (1 + t) / (1 - t) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
      _ = 2 * t / (1 - t) := by field_simp; ring
  have harc : Real.arctan t ≤ t / (1 - t) := by
    have hcont_inv : Continuous fun u : ℝ => 1 / (1 + u ^ 2) :=
      continuous_const.div (by fun_prop) (fun u => by positivity)
    have h1 : Real.arctan t ≤ t := by
      have h0 : 0 ≤ t := ht0.le
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := Real.arctan) (f' := fun u => 1 / (1 + u ^ 2)) (a := 0) (b := t)
        (fun u _ => Real.hasDerivAt_arctan u)
        (hcont_inv.intervalIntegrable 0 t)
      rw [Real.arctan_zero, sub_zero] at hFTC
      rw [← hFTC]
      calc ∫ u in (0 : ℝ)..t, 1 / (1 + u ^ 2)
          ≤ ∫ _u in (0 : ℝ)..t, (1 : ℝ) := by
            refine intervalIntegral.integral_mono_on h0
              (hcont_inv.intervalIntegrable 0 t)
              intervalIntegrable_const fun u _ => ?_
            exact div_le_one_of_le₀ (by nlinarith) (by positivity)
        _ = t := by simp
    have h2 : t ≤ t / (1 - t) :=
      le_div_self ht0.le h1mt (by linarith)
    exact h1.trans h2
  have hlin : (1 / 2 : ℝ) * (2 * t / (1 - t)) + t / (1 - t) = 2 * t / (1 - t) := by ring
  linarith

/-- Elementary lower bound `2 archLevyAntideriv y ≥ log((4 − y) / y)` for `0 < y < 2`. -/
theorem log_four_sub_div_le_two_mul_archLevyAntideriv {y : ℝ} (hy0 : 0 < y) (hy2 : y < 2) :
    Real.log ((4 - y) / y) ≤ 2 * archLevyAntideriv y := by
  rw [archLevyAntideriv_eq_log_div hy0]
  set t : ℝ := Real.exp (-y / 2) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hexp : 1 - y / 2 ≤ t := by
    have := Real.add_one_le_exp (-y / 2)
    linarith
  have harc : 0 < Real.arctan t := Real.arctan_pos.mpr ht0
  have h4y : 0 < 4 - y := by linarith
  have hlog : Real.log ((4 - y) / y) ≤ Real.log ((1 + t) / (1 - t)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ hy0 (by linarith)]
    nlinarith
  linarith

/-! ## Section 5: Boundary escape on `(0, L)` and unconditional short-support positivity -/

/-- If `h` vanishes outside `(0, L)`, then for every shift `x ≥ L`, `h(u) h(u + x) = 0`. -/
theorem mul_shift_eq_zero_of_support_Ioo {h : ℝ → ℝ} {L x : ℝ}
    (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hx : L ≤ x) (u : ℝ) :
    h u * h (u + x) = 0 := by
  by_cases hu : u ∈ Ioo 0 L
  · have hux : u + x ∉ Ioo 0 L := fun h' => by linarith [hu.1, h'.2]
    rw [hsupp (u + x) hux, mul_zero]
  · rw [hsupp u hu, zero_mul]

/-- If `h` is in `BddSupp A h C` and vanishes outside `(0, L)`, then for all `x ≥ L`,
`∫ (h(u) − h(u + x))² du = 2 ∫ h(u)² du`. -/
theorem integral_jump_sq_eq_two_mul_of_support_Ioo {A : Set ℝ} {h : ℝ → ℝ} {C L x : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hx : L ≤ x) :
    ∫ u, (h u - h (u + x)) ^ 2 = 2 * ∫ u, h u ^ 2 := by
  rw [integral_jump_sq hh x]
  have h0 : autocorr h x = 0 := by
    unfold autocorr
    simp_rw [mul_shift_eq_zero_of_support_Ioo hsupp hx]
    exact integral_zero ℝ ℝ
  rw [h0]
  ring

/-- For any `h` in `BddSupp A h C` vanishing outside `(0, L)` (`0 < L ≤ b`),
`2 (Ω(L) − Ω(b)) ∫ h² ≤ jumpEnergy h` in `ENNReal`. -/
theorem ofReal_two_mul_sub_archLevyAntideriv_le_jumpEnergy {A : Set ℝ} {h : ℝ → ℝ} {C L b : ℝ}
    (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) (hLb : L ≤ b) :
    ENNReal.ofReal (2 * (archLevyAntideriv L - archLevyAntideriv b) * ∫ u, h u ^ 2) ≤
      jumpEnergy h := by
  have hE0 : 0 ≤ ∫ u, h u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcont : ContinuousOn archLevyDensity (Icc L b) :=
    continuousOn_archLevyDensity.mono fun x hx => lt_of_lt_of_le hL hx.1
  have hintIoo : IntegrableOn (fun x => archLevyDensity x * (2 * ∫ u, h u ^ 2)) (Ioo L b) :=
    ((hcont.integrableOn_Icc).mono_set Ioo_subset_Icc_self).mul_const _
  have hnn : ∀ x ∈ Ioo L b, 0 ≤ archLevyDensity x * (2 * ∫ u, h u ^ 2) := fun x hx =>
    mul_nonneg (archLevyDensity_pos (lt_trans hL hx.1)).le (by positivity)
  have hval : (∫ x in Ioo L b, archLevyDensity x * (2 * ∫ u, h u ^ 2)) =
      2 * (archLevyAntideriv L - archLevyAntideriv b) * ∫ u, h u ^ 2 := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hLb,
      integral_archLevyDensity_Icc hL hLb]
    ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hintIoo
    ((ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall hnn))]
  calc ∫⁻ x in Ioo L b, ENNReal.ofReal (archLevyDensity x * (2 * ∫ u, h u ^ 2))
      = ∫⁻ x in Ioo L b, ENNReal.ofReal
          (archLevyDensity x * ∫ u, (h u - h (u + x)) ^ 2) := by
        refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        rw [integral_jump_sq_eq_two_mul_of_support_Ioo hh hsupp hx.1.le]
    _ ≤ jumpEnergy h :=
        lintegral_mono_set fun x hx => lt_trans hL hx.1

/-- Passing `b → ∞` gives `2 Ω(L) ∫ h² ≤ jumpEnergy h` for `h` vanishing outside `(0, L)`. -/
theorem ofReal_two_mul_archLevyAntideriv_le_jumpEnergy_of_support_Ioo {A : Set ℝ} {h : ℝ → ℝ}
    {C L : ℝ} (hh : BddSupp A h C) (hsupp : ∀ u ∉ Ioo 0 L, h u = 0) (hL : 0 < L) :
    ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, h u ^ 2) ≤ jumpEnergy h := by
  have hle : ∀ n : ℕ,
      ENNReal.ofReal (2 * (archLevyAntideriv L - archLevyAntideriv (L + n + 1)) * ∫ u, h u ^ 2) ≤
        jumpEnergy h := fun n => by
    have hLb : L ≤ L + (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    exact ofReal_two_mul_sub_archLevyAntideriv_le_jumpEnergy hh hsupp hL hLb
  have hlim : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (2 * (archLevyAntideriv L - archLevyAntideriv (L + n + 1)) *
        ∫ u, h u ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, h u ^ 2))) := by
    refine ENNReal.tendsto_ofReal (Tendsto.mul_const _ (Tendsto.const_mul 2 ?_))
    have h0 : Tendsto (fun n : ℕ => archLevyAntideriv (L + (n : ℝ) + 1)) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => (archLevyAntideriv_pos (by positivity)).le)
        (fun n => archLevyAntideriv_le (by positivity)) ?_
      have hexp0 : Tendsto (fun n : ℕ => Real.exp (-(L + (n : ℝ) + 1) / 2)) atTop (𝓝 0) := by
        rw [show (fun n : ℕ => Real.exp (-(L + (n : ℝ) + 1) / 2)) =
            fun n : ℕ => Real.exp (-((L + 1) / 2 + (n : ℝ) / 2)) by
          funext n; congr 1; ring]
        exact Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_const_nhds.add_atTop ((tendsto_natCast_atTop_iff (R := ℝ)).mpr tendsto_id
            |>.atTop_div_const two_pos))
      have hlim0 : (2 * (0 : ℝ)) / (1 - 0) = 0 := by ring
      rw [← hlim0]
      exact (hexp0.const_mul 2).div (tendsto_const_nhds.sub hexp0) (by norm_num)
    have hsub := (tendsto_const_nhds (x := archLevyAntideriv L)).sub h0
    rwa [sub_zero] at hsub
  exact le_of_tendsto hlim (Eventually.of_forall hle)

/-- **Quantile-rearranged jump energy lower bound for any nonnegative `g` with `|{g > 0}| ≤ L`.**
For any bounded measurable `g ≥ 0` whose positivity set `S = {x | 0 < g x}` has measure at most `L`,
`2 Ω(L) ∫ g² ≤ jumpEnergy g` in `ENNReal`. -/
theorem ofReal_two_mul_archLevyAntideriv_le_jumpEnergy_of_volume_pos_le {g : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {C L : ℝ} (hgC : ∀ x, g x ≤ C) (hL0 : 0 < L)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal L) :
    ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, g u ^ 2) ≤ jumpEnergy g := by
  set S := {x | 0 < g x}
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hg
  have hS : volume S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hgB : BddSupp S g C :=
    { meas := hg
      bound := fun x => by rw [abs_of_nonneg (hg0 x)]; exact hgC x
      supp := fun x hx => le_antisymm (not_lt.mp hx) (hg0 x)
      setm := hSm
      fin := hS }
  have hSL : (volume S).toReal ≤ L := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal hL0.le] at this
  have hTB := transport_bddSupp hSm hS hgB
  have hTB_L : BddSupp (Ioo 0 L) (transport hSm hS g) C :=
    { meas := hTB.meas
      bound := hTB.bound
      supp := fun x hx => Set.indicator_of_notMem (fun hx' => hx ⟨hx'.1, hx'.2.trans_le hSL⟩) _
      setm := measurableSet_Ioo
      fin := by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top }
  have h1 := ofReal_two_mul_archLevyAntideriv_le_jumpEnergy_of_support_Ioo hTB_L hTB_L.supp hL0
  rw [integral_sq_transport hSm hS hgB] at h1
  refine h1.trans ?_
  rw [jumpEnergy_eq, jumpEnergy_eq]
  exact lintegral_jump_transport_le hSm hS hgB hg0 measurable_jumpKernel jumpKernel_nonneg
    antitoneOn_jumpKernel integrableOn_min_jumpKernel

/-- **Unconditional `WeilEnergyNonneg` for any nonnegative `g` with `|{g > 0}| ≤ L` and
`-A(0) ≤ 2 Ω(L)`.** -/
theorem weilEnergyNonneg_of_volume_pos_le {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C L : ℝ} (hgC : ∀ x, g x ≤ C) (hL0 : 0 < L)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal L)
    (hΩ : -EF.gammaBracket 0 ≤ 2 * archLevyAntideriv L) :
    WeilEnergyNonneg g := by
  unfold WeilEnergyNonneg
  have hE0 : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 : ENNReal.ofReal (-EF.gammaBracket 0 * ∫ u, g u ^ 2) ≤
      ENNReal.ofReal (2 * archLevyAntideriv L * ∫ u, g u ^ 2) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hΩ hE0)
  have h2 := ofReal_two_mul_archLevyAntideriv_le_jumpEnergy_of_volume_pos_le hg hg0 hgC hL0 hvol
  exact (h1.trans h2).trans le_self_add

/-- Concrete unconditional verification that `-EF.gammaBracket 0 ≤ 2 Ω(L)` for all
`0 < L ≤ 1 / 130`. -/
theorem neg_gammaBracket_zero_le_two_mul_archLevyAntideriv {L : ℝ} (hL0 : 0 < L)
    (hL : L ≤ 1 / 130) :
    -EF.gammaBracket 0 ≤ 2 * archLevyAntideriv L := by
  have hA := neg_gammaBracket_zero_lt
  have hlow := log_four_sub_div_le_two_mul_archLevyAntideriv hL0 (by linarith)
  have h512 : (2 : ℝ) ^ (9 : ℕ) ≤ (4 - L) / L := by
    rw [le_div_iff₀ hL0]
    norm_num
    linarith
  have hlog9 : 9 * Real.log 2 ≤ Real.log ((4 - L) / L) := by
    have := Real.log_le_log (by positivity) h512
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hl2 := Real.log_two_gt_d9
  linarith

/-- **Unconditional `WeilEnergyNonneg` for any nonnegative `g` with `|{g > 0}| ≤ 1 / 130`.** -/
theorem weilEnergyNonneg_of_volume_pos_le_inv_130 {g : ℝ → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) {C : ℝ} (hgC : ∀ x, g x ≤ C)
    (hvol : volume {x | 0 < g x} ≤ ENNReal.ofReal (1 / 130)) :
    WeilEnergyNonneg g :=
  weilEnergyNonneg_of_volume_pos_le hg hg0 hgC (by norm_num) hvol
    (neg_gammaBracket_zero_le_two_mul_archLevyAntideriv (by norm_num) le_rfl)

/-- **Unconditional nonnegativity of `weilArchRe` for any nonnegative `f ∈ C²_c(ℝ)` with
`|{f > 0}| ≤ L` and `-A(0) ≤ 2 Ω(L)`.** -/
theorem weilArchRe_nonneg_of_volume_pos_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x) {L : ℝ} (hL0 : 0 < L)
    (hvol : volume {x | 0 < f x} ≤ ENNReal.ofReal L)
    (hΩ : -EF.gammaBracket 0 ≤ 2 * archLevyAntideriv L) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hc := hf.continuous
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, f x ≤ C := by
    obtain ⟨C, hC⟩ := hc.bddAbove_range_of_hasCompactSupport hfc
    exact ⟨C, fun x => hC ⟨x, rfl⟩⟩
  have hE := weilEnergyNonneg_of_volume_pos_le hc.measurable hf0 hC hL0 hvol hΩ
  rw [WeilLevyPole.weilArchRe_eq_levy_pole hf hfc]
  unfold WeilEnergyNonneg at hE
  have hJ := jumpEnergy_ne_top_of_smooth hf hfc
  rw [poleEnergy_eq_ofReal hc hfc hf0, ← ENNReal.ofReal_toReal hJ] at hE
  set J := (jumpEnergy f).toReal
  set P := ∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)
  have hP0 : 0 ≤ P :=
    integral_nonneg fun p => mul_nonneg (mul_nonneg (hf0 _) (hf0 _)) (Real.cosh_pos _).le
  have hJ0 : 0 ≤ J := ENNReal.toReal_nonneg
  rw [show (2 : ENNReal) * ENNReal.ofReal P = ENNReal.ofReal (2 * P) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat],
    ← ENNReal.ofReal_add hJ0 (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hE
  change 0 ≤ EF.gammaBracket 0 * (∫ u, f u ^ 2) + J + 2 * P
  linarith

/-- **Unconditional nonnegativity of `weilArchRe` for any nonnegative `f ∈ C²_c(ℝ)` with
`|{f > 0}| ≤ 1 / 130` (no `WindowPositive` hypothesis required).** -/
theorem weilArchRe_nonneg_of_volume_pos_le_inv_130 {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hf0 : ∀ x, 0 ≤ f x)
    (hvol : volume {x | 0 < f x} ≤ ENNReal.ofReal (1 / 130)) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) :=
  weilArchRe_nonneg_of_volume_pos_le hf hfc hf0 (by norm_num) hvol
    (neg_gammaBracket_zero_le_two_mul_archLevyAntideriv (by norm_num) le_rfl)

end

end RHTower.WeilLevyPoleGauss
