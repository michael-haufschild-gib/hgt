import GaloisForLFunctions.RHTower.Suzuki.SuzukiCarlemanFlatPortResponse

/-!
# The exact derivative rate of the flat Carleman port

The logistic kernel is a probability density and the flat profile varies slowly on the kernel's
scale, so the logistic average of the profile is asymptotically the profile itself:

`B'(L) / F(L) → 1`.

The comparison is uniform because `√L - √(L+y) ≤ |y|/2` for `L ≥ 4`, so the shifted ratio is
dominated by `exp(|y|/2)`, against which the logistic kernel's `exp(-|y|)` decay wins.  Since
`F(L) = exp(-√L)` beats every exponential weight in the wrong direction, no positive Gamma strip
survives: `exp(σL) B'(L)` is not square integrable for any `σ > 0`.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-- The two-sided exponential majorant is integrable. -/
theorem integrable_exp_neg_half_abs :
    Integrable (fun y : ℝ => Real.exp (-|y| / 2)) volume := by
  have hmeas : Measurable fun y : ℝ => Real.exp (-|y| / 2) := by fun_prop
  have hIoi : IntegrableOn (fun y : ℝ => Real.exp (-|y| / 2)) (Ioi 0) volume := by
    have hbase : IntegrableOn (fun y : ℝ => Real.exp (-(1/2) * y)) (Ioi (0:ℝ)) volume :=
      integrableOn_exp_mul_Ioi (by norm_num) 0
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hy0 : 0 ≤ y := le_of_lt hy
    show Real.exp (-(1/2) * y) = Real.exp (-|y| / 2)
    rw [abs_of_nonneg hy0]
    congr 1
    ring
  have hIic : IntegrableOn (fun y : ℝ => Real.exp (-|y| / 2)) (Iic 0) volume := by
    have hbase : IntegrableOn (fun y : ℝ => Real.exp ((1/2) * y)) (Iic (0:ℝ)) volume :=
      integrableOn_exp_mul_Iic (by norm_num) 0
    refine hbase.congr_fun ?_ measurableSet_Iic
    intro y hy
    have hy0 : y ≤ 0 := hy
    show Real.exp ((1/2) * y) = Real.exp (-|y| / 2)
    rw [abs_of_nonpos hy0]
    congr 1
    ring
  have hunion : IntegrableOn (fun y : ℝ => Real.exp (-|y| / 2)) (Iic 0 ∪ Ioi 0) volume :=
    hIic.union hIoi
  rwa [Iic_union_Ioi, integrableOn_univ] at hunion

theorem integrable_logisticKernel : Integrable logisticKernel volume := by
  refine Integrable.mono' integrable_exp_neg_half_abs
    continuous_logisticKernel.measurable.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (logisticKernel_pos y).le]
  refine le_trans (logisticKernel_le_exp_neg_abs y) ?_
  apply Real.exp_le_exp.mpr
  have := abs_nonneg y
  linarith

/-- **`(22)`: the logistic kernel is a probability density.** -/
theorem integral_logisticKernel : (∫ y, logisticKernel y) = 1 := by
  have hint := integrable_logisticKernel
  have hIoi : (∫ y in Ioi (0:ℝ), logisticKernel y) = 0 - logisticPrimitive 0 := by
    apply integral_Ioi_of_hasDerivAt_of_tendsto
      (hasDerivAt_logisticPrimitive 0).continuousAt.continuousWithinAt
      (fun x _ => hasDerivAt_logisticPrimitive x) hint.integrableOn
    have hexp : Tendsto (fun y : ℝ => (1 + Real.exp y)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => 1 + Real.exp y) atTop atTop :=
        tendsto_atTop_add_const_left _ 1 Real.tendsto_exp_atTop
      exact h1.inv_tendsto_atTop
    have hfun : logisticPrimitive = fun y : ℝ => -(1 + Real.exp y)⁻¹ := rfl
    rw [hfun]
    simpa using hexp.neg
  have hIic : (∫ y in Iic (0:ℝ), logisticKernel y) = logisticPrimitive 0 - (-1) := by
    apply integral_Iic_of_hasDerivAt_of_tendsto
      (hasDerivAt_logisticPrimitive 0).continuousAt.continuousWithinAt
      (fun x _ => hasDerivAt_logisticPrimitive x) hint.integrableOn
    have hexp : Tendsto (fun y : ℝ => (1 + Real.exp y)⁻¹) atBot (𝓝 1) := by
      have h1 : Tendsto (fun y : ℝ => 1 + Real.exp y) atBot (𝓝 1) := by
        have := Real.tendsto_exp_atBot
        simpa using this.const_add 1
      have h2 : Tendsto (fun y : ℝ => (1 + Real.exp y)⁻¹) atBot (𝓝 (1:ℝ)⁻¹) :=
        h1.inv₀ (by norm_num)
      simpa using h2
    have hfun : logisticPrimitive = fun y : ℝ => -(1 + Real.exp y)⁻¹ := rfl
    rw [hfun]
    simpa using hexp.neg
  have hsplit : (∫ y, logisticKernel y)
      = (∫ y in Iic (0:ℝ), logisticKernel y) + ∫ y in Ioi (0:ℝ), logisticKernel y := by
    rw [← setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Iic_union_Ioi, setIntegral_univ]
  rw [hsplit, hIoi, hIic]
  ring

/-- The shifted flat ratio is dominated by a half-exponential. -/
theorem flatPortProfile_ratio_le {L y : ℝ} (hL : 4 ≤ L) (hy : 0 < L + y) :
    flatPortProfile (L + y) / flatPortProfile L ≤ Real.exp (|y| / 2) := by
  have hLpos : (0:ℝ) < L := by linarith
  have hA : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
  have hB : Real.sqrt (L + y) * Real.sqrt (L + y) = L + y := Real.mul_self_sqrt hy.le
  have hA2 : (2:ℝ) ≤ Real.sqrt L := by
    have : Real.sqrt 4 ≤ Real.sqrt L := Real.sqrt_le_sqrt hL
    rwa [show (4:ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)] at this
  have hBnn : 0 ≤ Real.sqrt (L + y) := Real.sqrt_nonneg _
  have hkey : Real.sqrt L - Real.sqrt (L + y) ≤ |y| / 2 := by
    rcases le_total 0 y with hy0 | hy0
    · have hmono : Real.sqrt L ≤ Real.sqrt (L + y) := Real.sqrt_le_sqrt (by linarith)
      have : |y| = y := abs_of_nonneg hy0
      linarith
    · have habs : |y| = -y := abs_of_nonpos hy0
      have hmono : Real.sqrt (L + y) ≤ Real.sqrt L := Real.sqrt_le_sqrt (by linarith)
      nlinarith [hA, hB, hA2, hBnn]
  have hratio : flatPortProfile (L + y) / flatPortProfile L
      = Real.exp (Real.sqrt L - Real.sqrt (L + y)) := by
    rw [flatPortProfile, flatPortProfile, ← Real.exp_sub]
    congr 1
    ring
  rw [hratio]
  exact Real.exp_le_exp.mpr hkey

/-- For a fixed shift the flat ratio tends to one. -/
theorem tendsto_flatPortProfile_ratio (y : ℝ) :
    Tendsto (fun L : ℝ => flatPortProfile (L + y) / flatPortProfile L) atTop (𝓝 1) := by
  have hdiff : Tendsto (fun L : ℝ => Real.sqrt L - Real.sqrt (L + y)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ L : ℝ in atTop,
        ‖Real.sqrt L - Real.sqrt (L + y)‖ ≤ |y| / Real.sqrt L := by
      filter_upwards [eventually_gt_atTop (0:ℝ), eventually_gt_atTop (-y)] with L hL hLy
      have hLy' : 0 < L + y := by linarith
      have hA : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
      have hB : Real.sqrt (L + y) * Real.sqrt (L + y) = L + y := Real.mul_self_sqrt hLy'.le
      have hApos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
      have hBnn : 0 ≤ Real.sqrt (L + y) := Real.sqrt_nonneg _
      have hprod : (Real.sqrt L - Real.sqrt (L + y)) * (Real.sqrt L + Real.sqrt (L + y)) = -y := by
        nlinarith [hA, hB]
      rw [Real.norm_eq_abs, le_div_iff₀ hApos]
      calc |Real.sqrt L - Real.sqrt (L + y)| * Real.sqrt L
          ≤ |Real.sqrt L - Real.sqrt (L + y)| * (Real.sqrt L + Real.sqrt (L + y)) := by
            nlinarith [abs_nonneg (Real.sqrt L - Real.sqrt (L + y)), hBnn]
        _ = |(Real.sqrt L - Real.sqrt (L + y)) * (Real.sqrt L + Real.sqrt (L + y))| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt L + Real.sqrt (L + y))]
        _ = |(-y)| := by rw [hprod]
        _ = |y| := abs_neg y
    have hzero : Tendsto (fun L : ℝ => |y| / Real.sqrt L) atTop (𝓝 0) := by
      have h1 : Tendsto (fun L : ℝ => (Real.sqrt L)⁻¹) atTop (𝓝 0) :=
        Real.tendsto_sqrt_atTop.inv_tendsto_atTop
      have h2 := h1.const_mul |y|
      simpa [div_eq_mul_inv] using h2
    exact squeeze_zero_norm' hbound hzero
  have hexp : Tendsto (fun L : ℝ => Real.exp (Real.sqrt L - Real.sqrt (L + y))) atTop (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hdiff
    simpa [Function.comp_def] using h
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L _
  rw [flatPortProfile, flatPortProfile, ← Real.exp_sub]
  congr 1
  ring

end

end RHTower
