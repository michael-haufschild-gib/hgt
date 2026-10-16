import GaloisForLFunctions.RHTower.CHMDMasslessZeroWaveExplicitFormula
import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm

/-!
# CHMD: the archimedean place as a continuous prime distribution

The archimedean symbol `γ(r) = Re ψ(1/4 + ir/2) − log π` has the Lévy–Khintchine form
`γ(r) − γ(0) = 2 ∫_0^∞ ω(x)(1 − cos rx) dx`, `ω(x) = e^{−x/2}/(1 − e^{−2x})`.  Feeding it through the
sech² weight turns the massless archimedean wave into translates of the d'Alembert kernel
(`masslessArchWave_eq_levy`):

`(1/2π) ∫ cos(vr) sech²(r/2) γ(r) dr = γ(0) D(v) + ∫_0^∞ ω(x) (2D(v) − D(v+x) − D(v−x)) dx`.

So the massless Weil side is built entirely from translates of `D`
(`masslessWeilSide_eq_levy`): the primes put the masses `Λ(n)/√n` at the points `x = log n`, and the
archimedean place puts the continuous mass `ω(x) dx` on `(0, ∞)` with the compensator `2D(v)`:

`W₀(v) = (2/cos²(1/4)) cosh(v/2) + γ(0) D(v) + ∫_0^∞ ω(x)(2D(v) − D(v+x) − D(v−x)) dx
         − Σ_n (Λ(n)/√n)(D(v + log n) + D(v − log n))`.

The module also extends `ω` to the right half-plane (`levyDensityC`) and bounds the complex
d'Alembert kernel away from the imaginary axis (`norm_dAlembertKernel_le`), the two estimates used
to continue `W₀` across the boundary of the time strip.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped Real
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.EvenSector

/-! ## Elementary exponential bounds -/

theorem sq_le_thirtytwo_mul_exp (x : ℝ) : x ^ 2 ≤ 32 * Real.exp (|x| / 4) := by
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ |x| / 4)
  have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith [abs_nonneg x]

theorem sechSqHalf_mul_sq_le (r : ℝ) :
    sechSqHalf r * r ^ 2 / 2 ≤ 64 * Real.exp (-(3 / 4 * |r|)) := by
  have h1 := sechSqHalf_le_exp_neg_abs r
  have h2 := sq_le_thirtytwo_mul_exp r
  have hs := (sechSqHalf_pos r).le
  have hE : Real.exp (-|r|) * Real.exp (|r| / 4) = Real.exp (-(3 / 4 * |r|)) := by
    rw [← Real.exp_add]; ring_nf
  calc sechSqHalf r * r ^ 2 / 2 ≤ (4 * Real.exp (-|r|)) * (32 * Real.exp (|r| / 4)) / 2 := by
        gcongr
    _ = 64 * Real.exp (-(3 / 4 * |r|)) := by rw [← hE]; ring

theorem archLevyDensity_mul_sq_le {x : ℝ} (hx : 0 < x) :
    archLevyDensity x * x ^ 2 ≤ 34 * Real.exp (-(1 / 4) * x) := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have h2 : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-2 * x)
  have hden : 2 * x ≤ (1 - Real.exp (-2 * x)) * (1 + 2 * x) := by nlinarith
  have hlt : Real.exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-2 * x) := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ x / 4)
  have hpoly : x * (1 + 2 * x) / 2 ≤ 34 * Real.exp (x / 4) := by nlinarith
  have hE2 : Real.exp (-x / 2) * Real.exp (x / 4) = Real.exp (-(1 / 4) * x) := by
    rw [← Real.exp_add]; ring_nf
  unfold archLevyDensity
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have hex := Real.exp_pos (-x / 2)
  calc Real.exp (-x / 2) * x ^ 2
      = Real.exp (-x / 2) * (x * (2 * x)) / 2 := by ring
    _ ≤ Real.exp (-x / 2) * (x * ((1 - Real.exp (-2 * x)) * (1 + 2 * x))) / 2 := by gcongr
    _ = (Real.exp (-x / 2) * (x * (1 + 2 * x) / 2)) * (1 - Real.exp (-2 * x)) := by ring
    _ ≤ (Real.exp (-x / 2) * (34 * Real.exp (x / 4))) * (1 - Real.exp (-2 * x)) := by gcongr
    _ = 34 * Real.exp (-(1 / 4) * x) * (1 - Real.exp (-2 * x)) := by rw [← hE2]; ring

theorem integrableOn_archLevyDensity_mul_sq :
    IntegrableOn (fun x => |archLevyDensity x| * x ^ 2) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 34).mono'
    ((measurable_archLevyDensity.abs.mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (archLevyDensity_pos hx)]
  exact archLevyDensity_mul_sq_le hx

/-! ## The Lévy translate form of the massless archimedean wave -/

theorem gammaBracket_sub_zero_eq_integral (r : ℝ) :
    EF.gammaBracket r - EF.gammaBracket 0 =
      2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * (1 - Real.cos (r * x)) := by
  rw [WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate,
    WeilLevyPole.gammaBracket_eq_two_mul_gammaHardyPhaseRate, ← mul_sub,
    gammaHardyPhaseRate_sub_zero_eq_integral]

theorem one_sub_cos_le_sq_div_two (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

/-- The sech²-weighted Lévy integrand `cos(vr) sech²(r/2) ω(x)(1 − cos rx)`. -/
def levyTranslateIntegrand (v : ℝ) (r x : ℝ) : ℝ :=
  Real.cos (v * r) * sechSqHalf r * (archLevyDensity x * (1 - Real.cos (r * x)))

theorem integrable_levyTranslateIntegrand (v : ℝ) :
    Integrable (Function.uncurry (levyTranslateIntegrand v))
      (volume.prod (volume.restrict (Ioi 0))) := by
  set f := levyTranslateIntegrand v with hf
  have hg1 : Integrable fun r : ℝ => sechSqHalf r * r ^ 2 / 2 :=
    ((integrable_exp_neg_rate_abs (by norm_num : (0 : ℝ) < 3 / 4)).const_mul 64).mono'
      ((continuous_sechSqHalf.mul (continuous_pow 2)).div_const 2).aestronglyMeasurable
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by have := (sechSqHalf_pos r).le; positivity)]
        exact sechSqHalf_mul_sq_le r)
  refine (Integrable.mul_prod hg1 integrableOn_archLevyDensity_mul_sq).mono'
    ?_ (Eventually.of_forall fun p => ?_)
  · refine Measurable.aestronglyMeasurable ?_
    show Measurable fun p : ℝ × ℝ => Real.cos (v * p.1) * sechSqHalf p.1 *
      (archLevyDensity p.2 * (1 - Real.cos (p.1 * p.2)))
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.cos (v * p.1)).measurable.mul
      (continuous_sechSqHalf.measurable.comp measurable_fst)).mul
      ((measurable_archLevyDensity.comp measurable_snd).mul
        (by fun_prop : Continuous fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2)).measurable)
  · rcases p with ⟨r, x⟩
    simp only [hf, levyTranslateIntegrand, Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul]
    have hc : |Real.cos (v * r)| ≤ 1 := Real.abs_cos_le_one _
    have h1c : |1 - Real.cos (r * x)| ≤ (r * x) ^ 2 / 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
      exact one_sub_cos_le_sq_div_two _
    have hs := (sechSqHalf_pos r).le
    calc |Real.cos (v * r)| * |sechSqHalf r| * (|archLevyDensity x| * |1 - Real.cos (r * x)|)
        ≤ 1 * sechSqHalf r * (|archLevyDensity x| * ((r * x) ^ 2 / 2)) := by
          rw [abs_of_nonneg hs]
          gcongr
      _ = sechSqHalf r * r ^ 2 / 2 * (|archLevyDensity x| * x ^ 2) := by ring

theorem integral_levyTranslateIntegrand_inner (v x : ℝ) :
    ∫ r, levyTranslateIntegrand v r x =
      archLevyDensity x * (2 * π * dAlembertReal v - π * (dAlembertReal (v + x) +
        dAlembertReal (v - x))) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set f := levyTranslateIntegrand v with hf
  have hA : Integrable fun r => Real.cos (v * r) * sechSqHalf r :=
    (integrable_sechSqHalf_mul (g := fun r => Real.cos (v * r)) (by fun_prop)
      fun r => Real.abs_cos_le_one _).congr (Eventually.of_forall fun r => by ring)
  have hB : Integrable fun r => Real.cos (x * r) * sechSqHalf r * Real.cos (r * v) :=
    (integrable_sechSqHalf_mul (g := fun r => Real.cos (x * r) * Real.cos (r * v))
      (by fun_prop) fun r => by
        rw [abs_mul]; exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _)
          (Real.abs_cos_le_one _)).congr (Eventually.of_forall fun r => by ring)
  have e1 : ∫ r, Real.cos (v * r) * sechSqHalf r = 2 * π * dAlembertReal v := by
    rw [← integral_sechSqHalf_mul_cos_eq]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [mul_comm r v]; ring
  have e2 : ∫ r, Real.cos (x * r) * sechSqHalf r * Real.cos (r * v) =
      π * (dAlembertReal (v + x) + dAlembertReal (v - x)) := by
    rw [← integral_cos_mul_sechSqHalf_mul_cos x v, ← mul_assoc, mul_one_div_cancel hpi.ne',
      one_mul]
  calc ∫ r, f r x
      = ∫ r, archLevyDensity x * (Real.cos (v * r) * sechSqHalf r -
          Real.cos (x * r) * sechSqHalf r * Real.cos (r * v)) := by
        refine integral_congr_ae (Eventually.of_forall fun r => ?_)
        simp only [hf, levyTranslateIntegrand]
        rw [mul_comm r x, mul_comm r v]
        ring
    _ = _ := by rw [integral_const_mul, integral_sub hA hB, e1, e2]

/-- The Lévy translate integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_levyTranslate (v : ℝ) :
    IntegrableOn (fun x => archLevyDensity x *
      (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x))) (Ioi 0) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h := ((integrable_levyTranslateIntegrand v).integral_prod_right).const_mul (1 / π)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Function.uncurry_apply_pair]
  rw [integral_levyTranslateIntegrand_inner]
  field_simp
  ring

/-- **Lévy translate form**:
`(1/2π) A₀(v) = γ(0) D(v) + ∫_0^∞ ω(x) (2D(v) − D(v+x) − D(v−x)) dx`. -/
theorem masslessArchWave_eq_levy (v : ℝ) :
    1 / (2 * π) * masslessArchWave v = EF.gammaBracket 0 * dAlembertReal v +
      ∫ x in Ioi (0 : ℝ), archLevyDensity x *
        (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x)) := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  set f := levyTranslateIntegrand v with hf
  have hprod := integrable_levyTranslateIntegrand v
  have hswap := integral_integral_swap hprod
  have hinner := integral_levyTranslateIntegrand_inner v
  -- assemble
  have hout : ∫ r, Real.cos (v * r) * sechSqHalf r * EF.gammaBracket r =
      EF.gammaBracket 0 * (2 * π * dAlembertReal v) + 2 * ∫ r, ∫ x in Ioi (0 : ℝ), f r x := by
    have hA : Integrable fun r => Real.cos (v * r) * sechSqHalf r :=
      (integrable_sechSqHalf_mul (g := fun r => Real.cos (v * r)) (by fun_prop)
        fun r => Real.abs_cos_le_one _).congr (Eventually.of_forall fun r => by ring)
    have hI : Integrable fun r => ∫ x in Ioi (0 : ℝ), f r x := hprod.integral_prod_left
    have e1 : ∫ r, Real.cos (v * r) * sechSqHalf r = 2 * π * dAlembertReal v := by
      rw [← integral_sechSqHalf_mul_cos_eq]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp only
      rw [mul_comm r v]; ring
    calc ∫ r, Real.cos (v * r) * sechSqHalf r * EF.gammaBracket r
        = ∫ r, (EF.gammaBracket 0 * (Real.cos (v * r) * sechSqHalf r) +
            2 * ∫ x in Ioi (0 : ℝ), f r x) := by
          refine integral_congr_ae (Eventually.of_forall fun r => ?_)
          have hg := gammaBracket_sub_zero_eq_integral r
          simp only [hf, levyTranslateIntegrand]
          rw [integral_const_mul, show EF.gammaBracket r = EF.gammaBracket 0 +
            2 * ∫ x in Ioi (0 : ℝ), archLevyDensity x * (1 - Real.cos (r * x)) by linarith]
          ring
      _ = _ := by
          rw [integral_add (hA.const_mul _) (hI.const_mul _), integral_const_mul,
            integral_const_mul, e1]
  have hint : ∫ r, ∫ x in Ioi (0 : ℝ), f r x = ∫ x in Ioi (0 : ℝ), archLevyDensity x *
      (2 * π * dAlembertReal v - π * (dAlembertReal (v + x) + dAlembertReal (v - x))) := by
    rw [hswap]
    exact integral_congr_ae (Eventually.of_forall fun x => hinner x)
  unfold masslessArchWave
  rw [hout, hint]
  have hlin : ∫ x in Ioi (0 : ℝ), archLevyDensity x *
      (2 * π * dAlembertReal v - π * (dAlembertReal (v + x) + dAlembertReal (v - x))) =
      π * ∫ x in Ioi (0 : ℝ), archLevyDensity x *
        (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [hlin]
  field_simp

/-- **The massless Weil side in translate form.** -/
theorem masslessWeilSide_eq_levy (v : ℝ) :
    masslessWeilSide v = 2 / Real.cos (1 / 4 : ℝ) ^ 2 * Real.cosh (v / 2) +
      EF.gammaBracket 0 * dAlembertReal v +
      (∫ x in Ioi (0 : ℝ), archLevyDensity x *
        (2 * dAlembertReal v - dAlembertReal (v + x) - dAlembertReal (v - x))) -
      masslessPrimeWave v := by
  rw [masslessWeilSide, masslessArchWave_eq_levy]
  ring

/-! ## The Lévy density on the right half-plane -/

/-- The Lévy density `ω(u) = e^{−u/2}/(1 − e^{−2u})` of a complex variable. -/
def levyDensityC (u : ℂ) : ℂ := Complex.exp (-u / 2) / (1 - Complex.exp (-2 * u))

theorem levyDensityC_ofReal (x : ℝ) : levyDensityC x = (archLevyDensity x : ℂ) := by
  unfold levyDensityC archLevyDensity
  push_cast
  ring_nf

theorem one_sub_exp_ne_zero {u : ℂ} (hu : 0 < u.re) : 1 - Complex.exp (-2 * u) ≠ 0 := by
  intro h
  have h1 : ‖Complex.exp (-2 * u)‖ = 1 := by rw [← sub_eq_zero.mp h]; simp
  rw [Complex.norm_exp] at h1
  have : (-2 * u).re < 0 := by simp; linarith
  have := Real.exp_lt_one_iff.mpr this
  linarith

theorem differentiableAt_levyDensityC {u : ℂ} (hu : 0 < u.re) :
    DifferentiableAt ℂ levyDensityC u :=
  ((Complex.differentiable_exp.comp (by fun_prop : Differentiable ℂ fun u : ℂ => -u / 2)) u).div
    ((differentiableAt_const _).sub ((Complex.differentiable_exp.comp
      (by fun_prop : Differentiable ℂ fun u : ℂ => -2 * u)) u)) (one_sub_exp_ne_zero hu)

/-- `‖ω(u)‖ ≤ e^{−Re u/2}/(1 − e^{−2 Re u})` on the right half-plane. -/
theorem norm_levyDensityC_le {u : ℂ} (hu : 0 < u.re) :
    ‖levyDensityC u‖ ≤ Real.exp (-u.re / 2) / (1 - Real.exp (-2 * u.re)) := by
  have hlt : Real.exp (-2 * u.re) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold levyDensityC
  rw [norm_div, Complex.norm_exp]
  have hre : (-u / 2).re = -u.re / 2 := by simp [neg_div]
  rw [hre]
  refine div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith) ?_
  have h := norm_sub_norm_le (1 : ℂ) (Complex.exp (-2 * u))
  rw [norm_one, Complex.norm_exp] at h
  have hre2 : (-2 * u).re = -2 * u.re := by simp
  rw [hre2] at h
  linarith

/-! ## The complex d'Alembert kernel off the imaginary axis -/

theorem sinh_re_sq_le_norm_sinh_sq (w : ℂ) : Real.sinh w.re ^ 2 ≤ ‖Complex.sinh w‖ ^ 2 := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * I := (Complex.re_add_im w).symm
  have hs : Complex.sinh w = (Real.sinh w.re * Real.cos w.im : ℝ) +
      (Real.cosh w.re * Real.sin w.im : ℝ) * I := by
    conv_lhs => rw [hw]
    rw [Complex.sinh_add, Complex.sinh_mul_I, Complex.cosh_mul_I, ← Complex.ofReal_sinh,
      ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [hs, Complex.sq_norm, Complex.normSq_add_mul_I]
  have hc := Real.cosh_sq w.re
  have hp := Real.sin_sq_add_cos_sq w.im
  nlinarith [sq_nonneg (Real.sinh w.re), sq_nonneg (Real.sin w.im)]

/-- **Decay of the complex d'Alembert kernel**: for `π|Re w| ≥ 1`,
`‖D(w)‖ ≤ 8 ‖w‖ e^{−π|Re w|}`. -/
theorem norm_dAlembertKernel_le {w : ℂ} (hw : 1 ≤ π * |w.re|) :
    ‖dAlembertKernel w‖ ≤ 8 * ‖w‖ * Real.exp (-(π * |w.re|)) := by
  have hpi := Real.pi_pos
  have hre : w.re ≠ 0 := by
    intro h; rw [h, abs_zero, mul_zero] at hw; linarith
  have hw0 : w ≠ 0 := fun h => hre (by rw [h, zero_re])
  have hsinh := exp_div_four_le_sinh hw
  have hsabs : Real.sinh (π * |w.re|) ≤ ‖Complex.sinh (π * w)‖ := by
    have h := sinh_re_sq_le_norm_sinh_sq (π * w)
    have hre' : (↑π * w).re = π * w.re := by simp
    rw [hre'] at h
    have habs : |Real.sinh (π * w.re)| = Real.sinh (π * |w.re|) := by
      rcases le_or_gt 0 w.re with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]
      · rw [abs_of_neg h0, abs_of_neg (Real.sinh_neg_iff.mpr (by nlinarith)), ← Real.sinh_neg,
          mul_neg]
    have h2 : Real.sinh (π * |w.re|) ^ 2 ≤ ‖Complex.sinh (π * w)‖ ^ 2 := by
      rw [← habs, sq_abs]; exact h
    exact (pow_le_pow_iff_left₀ (Real.sinh_nonneg_iff.mpr (by positivity)) (norm_nonneg _)
      two_ne_zero).mp h2
  have hpos : 0 < Real.sinh (π * |w.re|) := lt_of_lt_of_le (by positivity) hsinh
  rw [dAlembertKernel_of_ne hw0, norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
    div_le_iff₀ (hpos.trans_le hsabs)]
  have hE : Real.exp (-(π * |w.re|)) * Real.exp (π * |w.re|) = 1 := by
    rw [← Real.exp_add]; simp
  have hE0 := Real.exp_pos (-(π * |w.re|))
  have hA : 8 * ‖w‖ * Real.exp (-(π * |w.re|)) * (Real.exp (π * |w.re|) / 4) ≤
      8 * ‖w‖ * Real.exp (-(π * |w.re|)) * ‖Complex.sinh (π * w)‖ :=
    mul_le_mul_of_nonneg_left (hsinh.trans hsabs) (by positivity)
  have hB : 8 * ‖w‖ * Real.exp (-(π * |w.re|)) * (Real.exp (π * |w.re|) / 4) = 2 * ‖w‖ := by
    linear_combination (2 * ‖w‖) * hE
  linarith

end RHTower.CHMDLightCone
