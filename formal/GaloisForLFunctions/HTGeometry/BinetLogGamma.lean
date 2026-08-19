import GaloisForLFunctions.HTGeometry.EulerMaclaurinSecondOrder

/-!
# Binet's first formula for the logarithm of the Gamma function

For `a > 0`,

```text
log Γ(a) = (a − 1/2) log a − a + (1/2) log (2π) − ∫_0^∞ P₂(x) (x+a)^{-2} dx,
```

with `P₂(x) = ({x}² − {x})/2` the periodic second Bernoulli half.  The proof applies second-order
Euler–Maclaurin to `x ↦ log (x + a)` on `[0, N]`, and identifies the limit through Euler's Gauss
product for `Γ` and Stirling's formula for `N!`; the `√(2π)` is exactly Stirling's constant.
-/

open Filter Real MeasureTheory Set intervalIntegral
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Derivatives of the shifted logarithm -/

theorem hasDerivAt_logShift {a x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => Real.log (y + a)) (1 / (x + a)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have h2 := (Real.hasDerivAt_log (ne_of_gt h)).comp x hb
  have hfun : (Real.log ∘ fun y : ℝ => y + a) = fun y : ℝ => Real.log (y + a) := rfl
  rw [hfun] at h2
  exact h2.congr_deriv (by field_simp)

theorem hasDerivAt_invShift {a x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => 1 / (y + a)) (-(1 / (x + a) ^ 2)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have := hb.inv (ne_of_gt h)
  rw [show (fun y : ℝ => 1 / (y + a)) = fun y : ℝ => (y + a)⁻¹ from funext fun y => one_div _]
  refine this.congr_deriv ?_
  field_simp

theorem hasDerivAt_logShiftPrimitive {a x : ℝ} (h : 0 < x + a) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a) - (y + a)) (Real.log (x + a)) x := by
  have hb : HasDerivAt (fun y : ℝ => y + a) 1 x := (hasDerivAt_id x).add_const a
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y + a)) (1 / (x + a)) x := hasDerivAt_logShift h
  have hmul := hb.mul hlog
  have hres := hmul.sub hb
  have hfun : (((fun y : ℝ => y + a) * fun y : ℝ => Real.log (y + a)) - fun y : ℝ => y + a)
      = fun y : ℝ => (y + a) * Real.log (y + a) - (y + a) := by
    funext y
    simp [Pi.sub_apply, Pi.mul_apply]
  rw [hfun] at hres
  refine hres.congr_deriv ?_
  field_simp
  ring

/-! ## The Binet kernel -/

/-- The Binet kernel `∫_0^∞ P₂(x)(x+a)^{-2} dx`. -/
def binetKernel (a : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), bernoulliHalfPer x / (x + a) ^ 2

theorem integrableOn_binetKernel {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => bernoulliHalfPer x / (x + a) ^ 2) (Ioi (0 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => bernoulliHalfPer x / (x + a) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_bernoulliHalfPer.div (by fun_prop)
  have hinv : IntegrableOn (fun x : ℝ => 1 / (x + a) ^ 2) (Ioi (0 : ℝ)) := by
    refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (g := fun x : ℝ => -(1 / (x + a)))
      (l := 0) ?_ ?_ ?_ ?_
    · have : ContinuousAt (fun x : ℝ => -(1 / (x + a))) 0 := by
        refine ContinuousAt.neg (ContinuousAt.div continuousAt_const (by fun_prop) ?_)
        simpa using ne_of_gt ha
      exact this.continuousWithinAt
    · intro x hx
      have hxa : (0 : ℝ) < x + a := by
        have : (0 : ℝ) < x := hx
        linarith
      have hd := (hasDerivAt_invShift hxa).neg
      exact hd.congr_deriv (by ring)
    · intro x hx
      have hxa : (0 : ℝ) < x + a := by
        have : (0 : ℝ) < x := hx
        linarith
      positivity
    · have hlim : Tendsto (fun x : ℝ => x + a) atTop atTop := tendsto_atTop_add_const_right _ a tendsto_id
      have hinv0 : Tendsto (fun x : ℝ => (x + a)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hlim
      have hneg : Tendsto (fun x : ℝ => -((x + a)⁻¹)) atTop (𝓝 (-0)) := hinv0.neg
      rw [neg_zero] at hneg
      refine hneg.congr fun x => ?_
      rw [one_div]
  have hdom : IntegrableOn (fun x : ℝ => (1 / 8) * (1 / (x + a) ^ 2)) (Ioi (0 : ℝ)) :=
    hinv.const_mul _
  refine Integrable.mono hdom hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hxa : (0 : ℝ) < x + a := by linarith
  have hker := abs_bernoulliHalfPer_le x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x + a) ^ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 8 : ℝ) * (1 / (x + a) ^ 2)),
    div_le_iff₀ (by positivity)]
  have hsimp : (1 / 8 : ℝ) * (1 / (x + a) ^ 2) * (x + a) ^ 2 = 1 / 8 := by
    field_simp
  rw [hsimp]
  exact hker

/-! ## Euler–Maclaurin applied to the shifted logarithm -/

/-- The truncated Binet kernel. -/
def binetKernelTrunc (a : ℝ) (N : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..(N : ℝ), bernoulliHalfPer x / (x + a) ^ 2

theorem sum_log_shift_eq {a : ℝ} (ha : 0 < a) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), Real.log ((m : ℝ) + a))
      = (((N : ℝ) + a) + 1 / 2) * Real.log ((N : ℝ) + a) - (N : ℝ)
        - a * Real.log a + Real.log a / 2 + binetKernelTrunc a N := by
  have hpos : ∀ x ∈ Ici (0 : ℝ), 0 < x + a := by
    intro x hx
    have : (0 : ℝ) ≤ x := hx
    linarith
  have hem := euler_maclaurin_second_order_real (f := fun y : ℝ => Real.log (y + a))
    (f' := fun y : ℝ => 1 / (y + a)) (f'' := fun y : ℝ => -(1 / (y + a) ^ 2)) N
    (fun x hx => hasDerivAt_logShift (hpos x hx))
    (fun x hx => hasDerivAt_invShift (hpos x hx))
    (by
      refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (by fun_prop) ?_)
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hpos x hx)))
  have hint : (∫ x in (0 : ℝ)..(N : ℝ), Real.log (x + a))
      = (((N : ℝ) + a) * Real.log ((N : ℝ) + a) - ((N : ℝ) + a))
        - (a * Real.log a - a) := by
    have hle : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hderiv : ∀ x ∈ uIcc (0 : ℝ) ((N : ℝ)),
        HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a) - (y + a)) (Real.log (x + a)) x := by
      intro x hx
      rw [uIcc_of_le hle] at hx
      exact hasDerivAt_logShiftPrimitive (by linarith [hx.1])
    have hii : IntervalIntegrable (fun x : ℝ => Real.log (x + a)) volume 0 ((N : ℝ)) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hle]
      refine ContinuousOn.log (by fun_prop) ?_
      intro x hx
      exact ne_of_gt (hpos x (le_trans hx.1 le_rfl))
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hii
    rw [this]
    norm_num
  have hker : (∫ x in (0 : ℝ)..(N : ℝ), bernoulliHalfPer x * -(1 / (x + a) ^ 2))
      = -binetKernelTrunc a N := by
    rw [binetKernelTrunc, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    field_simp
  rw [hint, hker] at hem
  rw [hem]
  simp only [zero_add]
  ring

/-! ## The three limits -/

theorem tendsto_binetKernelTrunc {a : ℝ} (ha : 0 < a) :
    Tendsto (binetKernelTrunc a) atTop (𝓝 (binetKernel a)) := by
  have := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
    (f := fun x : ℝ => bernoulliHalfPer x / (x + a) ^ 2) (μ := volume)
    (l := atTop) (b := fun N : ℕ => (N : ℝ)) (integrableOn_binetKernel ha)
    tendsto_natCast_atTop_atTop
  exact this

theorem tendsto_gaussLogSeq {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => a * Real.log (N : ℝ) + Real.log (Nat.factorial N)
        - ∑ m ∈ Finset.range (N + 1), Real.log ((m : ℝ) + a))
      atTop (𝓝 (Real.log (Real.Gamma a))) := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hlog : Tendsto (fun N : ℕ => Real.log (Real.GammaSeq a N)) atTop
      (𝓝 (Real.log (Real.Gamma a))) :=
    ((Real.continuousAt_log (ne_of_gt hΓ)).tendsto).comp (Real.GammaSeq_tendsto_Gamma a)
  refine hlog.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hprodpos : (0 : ℝ) < ∏ j ∈ Finset.range (N + 1), (a + (j : ℝ)) := by
    refine Finset.prod_pos fun j _ => ?_
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hfacpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hrpow : (0 : ℝ) < (N : ℝ) ^ a := Real.rpow_pos_of_pos hN0 a
  rw [Real.GammaSeq, Real.log_div (by positivity) (ne_of_gt hprodpos),
    Real.log_mul (ne_of_gt hrpow) (ne_of_gt hfacpos), Real.log_rpow hN0]
  have hlogprod : Real.log (∏ j ∈ Finset.range (N + 1), (a + (j : ℝ)))
      = ∑ m ∈ Finset.range (N + 1), Real.log ((m : ℝ) + a) := by
    rw [Real.log_prod]
    · exact Finset.sum_congr rfl fun j _ => by rw [add_comm]
    · intro j _
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      positivity
  rw [hlogprod]

theorem tendsto_stirlingCorrection :
    Tendsto (fun N : ℕ => Real.log (Nat.factorial N) - (((N : ℝ) + 1 / 2) * Real.log (N : ℝ) - N))
      atTop (𝓝 (Real.log (2 * π) / 2)) := by
  have hπ : (0 : ℝ) < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hstir : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N)) atTop
      (𝓝 (Real.log (Real.sqrt π))) :=
    ((Real.continuousAt_log (ne_of_gt hπ)).tendsto).comp Stirling.tendsto_stirlingSeq_sqrt_pi
  have hval : Real.log (Real.sqrt π) + Real.log 2 / 2 = Real.log (2 * π) / 2 := by
    rw [Real.log_sqrt Real.pi_pos.le, Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
    ring
  have hshift : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N) + Real.log 2 / 2) atTop
      (𝓝 (Real.log (2 * π) / 2)) := by
    rw [← hval]
    exact hstir.add tendsto_const_nhds
  refine hshift.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfacpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsq : (0 : ℝ) < Real.sqrt (2 * (N : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hdivpos : (0 : ℝ) < (N : ℝ) / Real.exp 1 := div_pos hN0 hepos
  rw [Stirling.stirlingSeq, Real.log_div (ne_of_gt hfacpos) (by positivity),
    Real.log_mul (ne_of_gt hsq) (by positivity), Real.log_sqrt (by linarith),
    Real.log_pow, Real.log_div (ne_of_gt hN0) (ne_of_gt hepos), Real.log_exp,
    Real.log_mul (by norm_num) (ne_of_gt hN0)]
  ring

theorem tendsto_shiftLogTerm {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => ((N : ℝ) + a + 1 / 2) * (Real.log (N : ℝ) - Real.log ((N : ℝ) + a)))
      atTop (𝓝 (-a)) := by
  have hderiv : HasDerivAt (fun u : ℝ => Real.log (1 + u)) 1 0 := by
    have h := hasDerivAt_logShift (a := (1 : ℝ)) (x := (0 : ℝ)) (by norm_num)
    have hfun : (fun y : ℝ => Real.log (y + 1)) = fun y : ℝ => Real.log (1 + y) := by
      funext y
      rw [add_comm]
    rw [hfun] at h
    exact h.congr_deriv (by norm_num)
  have hslope : Tendsto (fun u : ℝ => Real.log (1 + u) / u) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.mp hderiv
    refine this.congr fun u => ?_
    rw [slope_def_field]
    simp
  have hu : Tendsto (fun N : ℕ => a / (N : ℝ)) atTop (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_div_atTop_nhds_zero_nat a) ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    exact ne_of_gt (div_pos ha hN0)
  have hcomp : Tendsto (fun N : ℕ => Real.log (1 + a / (N : ℝ)) / (a / (N : ℝ))) atTop (𝓝 1) :=
    hslope.comp hu
  have hlin : Tendsto (fun N : ℕ => ((N : ℝ) + a + 1 / 2) * (a / (N : ℝ))) atTop (𝓝 a) := by
    have hrw : ∀ N : ℕ, 0 < N →
        ((N : ℝ) + a + 1 / 2) * (a / (N : ℝ)) = a + (a * (a + 1 / 2)) / (N : ℝ) := by
      intro N hN
      have hN0 : (0 : ℝ) ≠ (N : ℝ) := by
        have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        exact ne_of_lt this
      field_simp
      ring
    have hbase : Tendsto (fun N : ℕ => a + (a * (a + 1 / 2)) / (N : ℝ)) atTop (𝓝 (a + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at hbase
    refine hbase.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (hrw N hN).symm
  have hprod : Tendsto (fun N : ℕ =>
      (((N : ℝ) + a + 1 / 2) * (a / (N : ℝ))) *
        (Real.log (1 + a / (N : ℝ)) / (a / (N : ℝ)))) atTop (𝓝 (a * 1)) :=
    hlin.mul hcomp
  rw [mul_one] at hprod
  have hneg : Tendsto (fun N : ℕ =>
      -((((N : ℝ) + a + 1 / 2) * (a / (N : ℝ))) *
        (Real.log (1 + a / (N : ℝ)) / (a / (N : ℝ))))) atTop (𝓝 (-a)) := hprod.neg
  refine hneg.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : (0 : ℝ) < (N : ℝ) + a := by linarith
  have hane : a / (N : ℝ) ≠ 0 := ne_of_gt (div_pos ha hN0)
  have hlog : Real.log ((N : ℝ) + a) - Real.log (N : ℝ) = Real.log (1 + a / (N : ℝ)) := by
    rw [← Real.log_div (ne_of_gt hNa) (ne_of_gt hN0)]
    congr 1
    field_simp
  have hstep : (((N : ℝ) + a + 1 / 2) * (a / (N : ℝ))) *
      (Real.log (1 + a / (N : ℝ)) / (a / (N : ℝ)))
      = ((N : ℝ) + a + 1 / 2) * Real.log (1 + a / (N : ℝ)) := by
    field_simp
  rw [hstep, ← hlog]
  ring

/-! ## Binet's first formula -/

/-- **Binet's first formula.**  For `a > 0`,
`log Γ(a) = (a − 1/2) log a − a + (1/2) log (2π) − ∫_0^∞ P₂(x)(x+a)^{-2} dx`. -/
theorem log_Gamma_eq_binet {a : ℝ} (ha : 0 < a) :
    Real.log (Real.Gamma a)
      = (a - 1 / 2) * Real.log a - a + Real.log (2 * π) / 2 - binetKernel a := by
  set C : ℕ → ℝ := fun N => a * Real.log (N : ℝ) + Real.log (Nat.factorial N)
    - ∑ m ∈ Finset.range (N + 1), Real.log ((m : ℝ) + a) with hC
  have hlim1 : Tendsto C atTop (𝓝 (Real.log (Real.Gamma a))) := tendsto_gaussLogSeq ha
  have hlim2 : Tendsto C atTop
      (𝓝 (Real.log (2 * π) / 2 + -a + (a * Real.log a - Real.log a / 2 - binetKernel a))) := by
    have hsum := ((tendsto_stirlingCorrection.add (tendsto_shiftLogTerm ha)).add
      ((tendsto_const_nhds (x := a * Real.log a - Real.log a / 2)).sub
        (tendsto_binetKernelTrunc ha)))
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hsl := sum_log_shift_eq ha N
    rw [hC]
    simp only
    rw [hsl]
    ring
  have := tendsto_nhds_unique hlim1 hlim2
  rw [this]
  ring

/-- Binet's formula in exponential form: `Γ(a) = √(2π) a^{a−1/2} e^{−a} e^{−K(a)}`. -/
theorem Gamma_eq_binet_exp {a : ℝ} (ha : 0 < a) :
    Real.Gamma a = Real.sqrt (2 * π) * a ^ (a - 1 / 2) * Real.exp (-a) * Real.exp (-binetKernel a) := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hlog := log_Gamma_eq_binet ha
  have hrhs : Real.log (Real.sqrt (2 * π) * a ^ (a - 1 / 2) * Real.exp (-a) *
      Real.exp (-binetKernel a))
      = (a - 1 / 2) * Real.log a - a + Real.log (2 * π) / 2 - binetKernel a := by
    have h2π : (0 : ℝ) < 2 * π := by positivity
    rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
      Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
      Real.log_mul (ne_of_gt (Real.sqrt_pos.mpr h2π)) (ne_of_gt (Real.rpow_pos_of_pos ha _)),
      Real.log_sqrt h2π.le, Real.log_rpow ha, Real.log_exp, Real.log_exp]
    ring
  have hposR : (0 : ℝ) < Real.sqrt (2 * π) * a ^ (a - 1 / 2) * Real.exp (-a) *
      Real.exp (-binetKernel a) := by
    have h2π : (0 : ℝ) < 2 * π := by positivity
    have := Real.sqrt_pos.mpr h2π
    have := Real.rpow_pos_of_pos ha (a - 1 / 2)
    positivity
  have hlogeq : Real.log (Real.Gamma a)
      = Real.log (Real.sqrt (2 * π) * a ^ (a - 1 / 2) * Real.exp (-a) *
          Real.exp (-binetKernel a)) := by
    rw [hlog, hrhs]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hΓ) (Set.mem_Ioi.mpr hposR) hlogeq

end

end GaloisForLFunctions.HTGeometry
