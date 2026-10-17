import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicShiftCommutatorAndParityIntertwining

/-!
# Pillar IX: Functional-Equation Dual & Cosecant–Secant Decomposition of the Archimedean Kernel

This module establishes the **Exact Functional-Equation Dual & Cosecant–Secant Kernel
Decomposition** of `archLevySinhWeight` inside `GaloisForLFunctions.BiScaleUncertainty`,
unifying the singular origin Lévy pole of the Even Sector (`EWU`) with the smooth hyperbolic
secant kernel `sech(x/2) = 1 / cosh(x/2)` of the Odd Sector (`OWU` / `HF`).

## Main Results

1. **Exact Half-Angle Cosecant–Secant Decomposition (`archLevySinhWeight_eq_half_csch_add_half_sech`
   & `archDualLevySinhWeight_eq_half_csch_sub_half_sech`):**
   For every `x ≠ 0`:
   `e^{x/2} / sinh x = 1 / (2 sinh(x/2)) + 1 / (2 cosh(x/2))` and
   `e^{-x/2} / sinh x = 1 / (2 sinh(x/2)) - 1 / (2 cosh(x/2))`.
2. **Exact Forward–Dual Secant Decomposition (`archLevySinhWeight_eq_sech_add_dual`):**
   In logarithmic coordinates `x = log t`, the time-reversal (functional-equation) involution
   `t ↦ 1/t` corresponds to `x ↦ -x`, which replaces the forward weight `w_+(x) = e^{x/2} / sinh x`
   by the strictly positive dual weight `w_-(x) = e^{-x/2} / sinh x`. Their difference is the
   everywhere-smooth positive-definite hyperbolic secant kernel `sech(x/2) = 1 / cosh(x/2)`:
   `archLevySinhWeight x = archSechHalfWeight x + archDualLevySinhWeight x`.
3. **Exact Positive Energy Splitting (`biScaleLevyEnergy_eq_secant_add_dual`,
   `biScaleSecantEnergy_le_biScaleLevyEnergy`, `biScaleDualLevyEnergy_le_biScaleLevyEnergy`):**
   For every `f ∈ C²_c(ℝ)`, the Bi-Scale Lévy energy splits into the sum of two nonnegative
   functionals:
   `biScaleLevyEnergy f = biScaleSecantEnergy f + biScaleDualLevyEnergy f`,
   where `biScaleSecantEnergy f = ∫_{(0, ∞)} (h(0) - h(x)) / cosh(x/2) dx ≥ 0` and
   `biScaleDualLevyEnergy f = ∫_{(0, ∞)} (h(0) - h(x)) (e^{-x/2} / sinh x) dx ≥ 0`.
4. **Hyperbolic Multiplier Intertwining of the Secant Kernel
   (`autocorr_mul_archSechHalfWeight_eq_cosh_sub_sinh`):**
   Combining `archSechHalfWeight x = 1 / cosh(x/2)` with Pillar VI's
   `autocorr_coshMultiplier_sub_sinhMultiplier` at `α = 1/2` proves that for all `x ∈ ℝ`:
   `autocorr f x * archSechHalfWeight x = (autocorr (coshMultiplier (1/2) f) x - autocorr (sinhMultiplier (1/2) f) x) / cosh(x/2)^2`.
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. Component Kernels & Exact Pointwise Hyperbolic Decompositions -/

/-- The smooth, positive-definite hyperbolic secant weight `w_sech(x) = 1 / cosh(x/2)`. -/
def archSechHalfWeight (x : ℝ) : ℝ :=
  1 / Real.cosh (x / 2)

/-- The time-reversed (functional-equation dual) archimedean Lévy weight
`w_dual(x) = e^{-x/2} / sinh x`. -/
def archDualLevySinhWeight (x : ℝ) : ℝ :=
  Real.exp (-x / 2) / Real.sinh x

/-- The singular half-angle hyperbolic cosecant weight `w_csch(x) = 1 / (2 sinh(x/2))`. -/
def archHalfCschWeight (x : ℝ) : ℝ :=
  1 / (2 * Real.sinh (x / 2))

theorem archSechHalfWeight_pos (x : ℝ) : 0 < archSechHalfWeight x :=
  div_pos one_pos (Real.cosh_pos _)

theorem archDualLevySinhWeight_pos {x : ℝ} (hx : 0 < x) : 0 < archDualLevySinhWeight x :=
  div_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr hx)

theorem archHalfCschWeight_pos {x : ℝ} (hx : 0 < x) : 0 < archHalfCschWeight x :=
  div_pos one_pos (mul_pos two_pos (Real.sinh_pos_iff.mpr (half_pos hx)))

/-- Double-angle identity for `sinh`: `sinh x = 2 * sinh(x/2) * cosh(x/2)`. -/
theorem sinh_eq_two_mul_sinh_half_mul_cosh_half (x : ℝ) :
    Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
  set t := x / 2
  have ht2 : -x = -t + -t := by dsimp [t]; ring
  have ht1 : x = t + t := by dsimp [t]; ring
  rw [Real.sinh_eq, Real.sinh_eq, Real.cosh_eq, ht2, ht1, Real.exp_add, Real.exp_add]
  ring

/-- Exponential half-angle decomposition: `exp(x/2) = cosh(x/2) + sinh(x/2)`. -/
theorem exp_half_eq_cosh_half_add_sinh_half (x : ℝ) :
    Real.exp (x / 2) = Real.cosh (x / 2) + Real.sinh (x / 2) := by
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Negative exponential half-angle decomposition: `exp(-x/2) = cosh(x/2) - sinh(x/2)`. -/
theorem exp_neg_half_eq_cosh_half_sub_sinh_half (x : ℝ) :
    Real.exp (-x / 2) = Real.cosh (x / 2) - Real.sinh (x / 2) := by
  rw [Real.cosh_eq, Real.sinh_eq, show -x / 2 = -(x / 2) by ring]
  ring

/-- **Exact Cosecant–Secant Half-Angle Decomposition of `archLevySinhWeight`:**
For every `x ≠ 0`,
`e^{x/2} / sinh x = 1 / (2 sinh(x/2)) + 1 / (2 cosh(x/2))`. -/
theorem archLevySinhWeight_eq_half_csch_add_half_sech {x : ℝ} (hx : x ≠ 0) :
    archLevySinhWeight x = archHalfCschWeight x + archSechHalfWeight x / 2 := by
  unfold archLevySinhWeight archHalfCschWeight archSechHalfWeight
  rw [exp_half_eq_cosh_half_add_sinh_half x, sinh_eq_two_mul_sinh_half_mul_cosh_half x]
  have hsinh : Real.sinh (x / 2) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]
    exact div_ne_zero hx two_ne_zero
  have hcosh : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp [hsinh, hcosh]

/-- **Exact Cosecant–Secant Half-Angle Decomposition of `archDualLevySinhWeight`:**
For every `x ≠ 0`,
`e^{-x/2} / sinh x = 1 / (2 sinh(x/2)) - 1 / (2 cosh(x/2))`. -/
theorem archDualLevySinhWeight_eq_half_csch_sub_half_sech {x : ℝ} (hx : x ≠ 0) :
    archDualLevySinhWeight x = archHalfCschWeight x - archSechHalfWeight x / 2 := by
  unfold archDualLevySinhWeight archHalfCschWeight archSechHalfWeight
  rw [exp_neg_half_eq_cosh_half_sub_sinh_half x, sinh_eq_two_mul_sinh_half_mul_cosh_half x]
  have hsinh : Real.sinh (x / 2) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]
    exact div_ne_zero hx two_ne_zero
  have hcosh : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp [hsinh, hcosh]

/-- **Exact Forward–Dual Secant Decomposition of `archLevySinhWeight`:**
For every `x ∈ ℝ`,
`archLevySinhWeight x = if x = 0 then 0 else archSechHalfWeight x + archDualLevySinhWeight x`,
and for all `x ≠ 0`:
`e^{x/2} / sinh x = 1 / cosh(x/2) + e^{-x/2} / sinh x`. -/
theorem archLevySinhWeight_eq_sech_add_dual {x : ℝ} (hx : x ≠ 0) :
    archLevySinhWeight x = archSechHalfWeight x + archDualLevySinhWeight x := by
  rw [archLevySinhWeight_eq_half_csch_add_half_sech hx,
    archDualLevySinhWeight_eq_half_csch_sub_half_sech hx]
  ring

/-- On `(0, ∞)`, both `archSechHalfWeight x` and `archDualLevySinhWeight x` are strictly smaller
than `archLevySinhWeight x`. -/
theorem archSechHalfWeight_lt_archLevySinhWeight {x : ℝ} (hx : 0 < x) :
    archSechHalfWeight x < archLevySinhWeight x := by
  rw [archLevySinhWeight_eq_sech_add_dual hx.ne']
  linarith [archDualLevySinhWeight_pos hx]

theorem archDualLevySinhWeight_lt_archLevySinhWeight {x : ℝ} (hx : 0 < x) :
    archDualLevySinhWeight x < archLevySinhWeight x := by
  rw [archLevySinhWeight_eq_sech_add_dual hx.ne']
  linarith [archSechHalfWeight_pos x]

/-! ## §2. Exact Positive Splitting of `biScaleLevyEnergy` into Secant & Dual Energies -/

/-- The **Bi-Scale Hyperbolic Secant Increment Energy**:
`𝒥_sech(f) = ∫ x in Ioi 0, (h(0) - h(x)) / cosh(x/2)`. -/
def biScaleSecantEnergy (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi 0, (autocorr f 0 - autocorr f x) * archSechHalfWeight x

/-- The **Time-Reversed (Functional-Equation Dual) Bi-Scale Lévy Energy**:
`𝒥_dual(f) = ∫ x in Ioi 0, (h(0) - h(x)) * (e^{-x/2} / sinh x)`. -/
def biScaleDualLevyEnergy (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi 0, (autocorr f 0 - autocorr f x) * archDualLevySinhWeight x

/-- Integrability of the hyperbolic secant increment integrand on `(0, ∞)` for `f ∈ C²_c(ℝ)`. -/
theorem integrableOn_biScaleSecantIntegrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archSechHalfWeight x) (Ioi 0) := by
  have harch := integrableOn_biScaleLevyIntegrand hf hfc
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hmeas :
      AEStronglyMeasurable
        (fun x => (autocorr f 0 - autocorr f x) * archSechHalfWeight x)
        (volume.restrict (Ioi 0)) := by
    refine Continuous.aestronglyMeasurable ?_
    refine (continuous_const.sub hc).mul ?_
    unfold archSechHalfWeight
    exact continuous_const.div (Real.continuous_cosh.comp (continuous_id.div_const 2))
      fun x => (Real.cosh_pos _).ne'
  refine harch.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hsub := autocorr_sub_nonneg hfc hf.continuous x
  have hsech := (archSechHalfWeight_pos x).le
  have hlt := (archSechHalfWeight_lt_archLevySinhWeight hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsub hsech)]
  exact mul_le_mul_of_nonneg_left hlt hsub

/-- Integrability of the dual Lévy increment integrand on `(0, ∞)` for `f ∈ C²_c(ℝ)`. -/
theorem integrableOn_biScaleDualLevyIntegrand {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archDualLevySinhWeight x) (Ioi 0) := by
  have harch := integrableOn_biScaleLevyIntegrand hf hfc
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hmeas :
      AEStronglyMeasurable
        (fun x => (autocorr f 0 - autocorr f x) * archDualLevySinhWeight x)
        (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_const.sub hc.continuousOn).mul ?_
    unfold archDualLevySinhWeight
    exact (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).continuousOn.div
      Real.continuous_sinh.continuousOn fun x hx => (Real.sinh_pos_iff.mpr hx).ne'
  refine harch.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hsub := autocorr_sub_nonneg hfc hf.continuous x
  have hdual := (archDualLevySinhWeight_pos hx).le
  have hlt := (archDualLevySinhWeight_lt_archLevySinhWeight hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hsub hdual)]
  exact mul_le_mul_of_nonneg_left hlt hsub

theorem biScaleSecantEnergy_nonneg {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) :
    0 ≤ biScaleSecantEnergy f := by
  unfold biScaleSecantEnergy
  refine setIntegral_nonneg measurableSet_Ioi fun x _ => ?_
  exact mul_nonneg (autocorr_sub_nonneg hfc hf x) (archSechHalfWeight_pos x).le

theorem biScaleDualLevyEnergy_nonneg {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) :
    0 ≤ biScaleDualLevyEnergy f := by
  unfold biScaleDualLevyEnergy
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  exact mul_nonneg (autocorr_sub_nonneg hfc hf x) (archDualLevySinhWeight_pos hx).le

/-- **Exact Functional-Equation Energy Splitting of `biScaleLevyEnergy`:**
For every `f ∈ C²_c(ℝ)`,
`biScaleLevyEnergy f = biScaleSecantEnergy f + biScaleDualLevyEnergy f`. -/
theorem biScaleLevyEnergy_eq_secant_add_dual {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    biScaleLevyEnergy f = biScaleSecantEnergy f + biScaleDualLevyEnergy f := by
  have hi_s := integrableOn_biScaleSecantIntegrand hf hfc
  have hi_d := integrableOn_biScaleDualLevyIntegrand hf hfc
  unfold biScaleLevyEnergy biScaleSecantEnergy biScaleDualLevyEnergy
  rw [← integral_add hi_s hi_d]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [archLevySinhWeight_eq_sech_add_dual (mem_Ioi.mp hx).ne']
  ring

theorem biScaleSecantEnergy_le_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    biScaleSecantEnergy f ≤ biScaleLevyEnergy f := by
  rw [biScaleLevyEnergy_eq_secant_add_dual hf hfc]
  linarith [biScaleDualLevyEnergy_nonneg hfc hf.continuous]

theorem biScaleDualLevyEnergy_le_biScaleLevyEnergy {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    biScaleDualLevyEnergy f ≤ biScaleLevyEnergy f := by
  rw [biScaleLevyEnergy_eq_secant_add_dual hf hfc]
  linarith [biScaleSecantEnergy_nonneg hfc hf.continuous]

/-! ## §3. Intertwining the Secant Kernel with Hyperbolic Multipliers (`α = 1/2`) -/

/-- **Secant–Hyperbolic Multiplier Intertwining Identity:**
Combining `archSechHalfWeight x = 1 / cosh(x/2)` with Pillar VI's
`autocorr_coshMultiplier_sub_sinhMultiplier` at `α = 1/2` expresses the secant-weighted
autocorrelation in terms of the squared hyperbolic secant `1 / cosh(x/2)^2`:
`autocorr f x * archSechHalfWeight x = (autocorr (coshMultiplier (1/2) f) x - autocorr (sinhMultiplier (1/2) f) x) / cosh(x/2)^2`. -/
theorem autocorr_mul_archSechHalfWeight_eq_cosh_sub_sinh {f : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : ℝ) :
    autocorr f x * archSechHalfWeight x =
      (autocorr (coshMultiplier (1 / 2) f) x -
        autocorr (sinhMultiplier (1 / 2) f) x) /
        Real.cosh (x / 2) ^ 2 := by
  have hint := autocorr_coshMultiplier_sub_sinhMultiplier hf hfc (1 / 2) x
  have harg : (1 / 2 : ℝ) * x = x / 2 := by ring
  rw [harg] at hint
  rw [hint]
  unfold archSechHalfWeight
  have hcosh : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp [hcosh]

end

end GaloisForLFunctions.BiScaleUncertainty
