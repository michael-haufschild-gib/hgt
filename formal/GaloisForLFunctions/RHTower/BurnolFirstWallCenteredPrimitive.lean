import GaloisForLFunctions.RHTower.BurnolFirstWallSourceDecay

/-!
# The centred and second primitives of the two-scale coboundary

The primitive `P(t) = ∫_0^t p` of the coboundary `p(t) = fract t - fract 2t` is one-periodic and
bounded, but it does not have mean zero over a cell.  Subtracting its cell mean
`m = ∫_0^(1 : ℕ) P` produces the **centred primitive** `P₀ = P - m`, which is again one-periodic, has the
same right derivative `p`, and integrates to zero over every cell.  Its own primitive
`P₁(t) = ∫_0^t P₀` is therefore one-periodic and bounded as well.

Two integrations by parts against `y^{-ρ-1}` now gain two powers instead of one:

`∫_t^∞ p(y) y^{-ρ-1} dy = -P₀(t) t^{-ρ-1} + (ρ+1) ∫_t^∞ P₀(y) y^{-ρ-2} dy`,

`∫_t^∞ P₀(y) y^{-ρ-2} dy = -P₁(t) t^{-ρ-2} + (ρ+2) ∫_t^∞ P₁(y) y^{-ρ-3} dy`.

The second identity makes the tail moment of `P₀` itself `O(t^{-σ-2})`, one order better than the
trivial estimate.  Both boundary terms at infinity vanish because `P₀` and `P₁` are bounded.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

noncomputable section

namespace RHTower

/-! ## The centred primitive -/

/-- The cell mean of the periodic primitive of the two-scale coboundary. -/
def burnolPrimitiveMean : ℝ := ∫ y in (0 : ℝ)..1, burnolFractPairPrimitive y

theorem abs_burnolPrimitiveMean_le_one : |burnolPrimitiveMean| ≤ 1 := by
  have hbound : ‖∫ y in (0 : ℝ)..1, burnolFractPairPrimitive y‖ ≤ 1 * |(1 : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by
      rw [Real.norm_eq_abs]; exact abs_burnolFractPairPrimitive_le_one x
  rw [Real.norm_eq_abs] at hbound
  rw [burnolPrimitiveMean]
  norm_num at hbound
  exact hbound

/-- The centred primitive `P₀ = P - m`, one-periodic with mean zero over a cell. -/
def burnolCenteredPrimitive (t : ℝ) : ℝ := burnolFractPairPrimitive t - burnolPrimitiveMean

theorem continuous_burnolCenteredPrimitive : Continuous burnolCenteredPrimitive :=
  continuous_burnolFractPairPrimitive.sub continuous_const

theorem intervalIntegrable_burnolCenteredPrimitive (a b : ℝ) :
    IntervalIntegrable burnolCenteredPrimitive volume a b :=
  continuous_burnolCenteredPrimitive.intervalIntegrable a b

/-- **The centred primitive has the same right derivative as the primitive.** -/
theorem hasDerivWithinAt_burnolCenteredPrimitive (a : ℝ) :
    HasDerivWithinAt burnolCenteredPrimitive (burnolFractPair a) (Ici a) a :=
  (hasDerivWithinAt_burnolFractPairPrimitive a).sub_const burnolPrimitiveMean

theorem burnolCenteredPrimitive_periodic : Function.Periodic burnolCenteredPrimitive 1 := by
  intro t
  rw [burnolCenteredPrimitive, burnolCenteredPrimitive, burnolFractPairPrimitive_periodic t]

theorem abs_burnolCenteredPrimitive_le_two (t : ℝ) : |burnolCenteredPrimitive t| ≤ 2 := by
  have h1 := abs_burnolFractPairPrimitive_le_one t
  have h2 := abs_burnolPrimitiveMean_le_one
  rw [abs_le] at h1 h2
  rw [burnolCenteredPrimitive, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **The centred primitive has mean zero.** -/
theorem integral_burnolCenteredPrimitive_unit :
    (∫ y in (0 : ℝ)..1, burnolCenteredPrimitive y) = 0 := by
  have hsub : (∫ y in (0 : ℝ)..1, burnolCenteredPrimitive y) =
      (∫ y in (0 : ℝ)..1, burnolFractPairPrimitive y) -
        ∫ _y in (0 : ℝ)..1, burnolPrimitiveMean := by
    rw [← intervalIntegral.integral_sub
      (continuous_burnolFractPairPrimitive.intervalIntegrable 0 1)
      (intervalIntegrable_const)]
    rfl
  rw [hsub, intervalIntegral.integral_const, burnolPrimitiveMean]
  simp

/-! ## The second primitive -/

/-- The second primitive `P₁(t) = ∫_0^t P₀`, one-periodic and bounded. -/
def burnolSecondPrimitive (t : ℝ) : ℝ := ∫ y in (0 : ℝ)..t, burnolCenteredPrimitive y

theorem continuous_burnolSecondPrimitive : Continuous burnolSecondPrimitive :=
  intervalIntegral.continuous_primitive intervalIntegrable_burnolCenteredPrimitive 0

theorem hasDerivAt_burnolSecondPrimitive (a : ℝ) :
    HasDerivAt burnolSecondPrimitive (burnolCenteredPrimitive a) a :=
  intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_burnolCenteredPrimitive 0 a)
    (continuous_burnolCenteredPrimitive.stronglyMeasurableAtFilter volume (𝓝 a))
    continuous_burnolCenteredPrimitive.continuousAt

theorem burnolSecondPrimitive_periodic : Function.Periodic burnolSecondPrimitive 1 := by
  intro t
  have hsplit : burnolSecondPrimitive t + (∫ y in t..(t + 1), burnolCenteredPrimitive y) =
      burnolSecondPrimitive (t + 1) :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_burnolCenteredPrimitive 0 t)
      (intervalIntegrable_burnolCenteredPrimitive t (t + 1))
  have hcell : (∫ y in t..(t + 1), burnolCenteredPrimitive y) = 0 := by
    have h := burnolCenteredPrimitive_periodic.intervalIntegral_add_eq t 0
    rw [zero_add] at h
    rw [h, integral_burnolCenteredPrimitive_unit]
  rw [← hsplit, hcell, add_zero]

theorem abs_burnolSecondPrimitive_le_two (t : ℝ) : |burnolSecondPrimitive t| ≤ 2 := by
  have hred : burnolSecondPrimitive t = burnolSecondPrimitive (Int.fract t) := by
    have h := burnolSecondPrimitive_periodic.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at h
    rw [Int.fract, h]
  rw [hred, burnolSecondPrimitive]
  have hbound : ‖∫ y in (0 : ℝ)..Int.fract t, burnolCenteredPrimitive y‖ ≤
      2 * |Int.fract t - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => by
      rw [Real.norm_eq_abs]; exact abs_burnolCenteredPrimitive_le_two x
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (Int.fract_nonneg t)] at hbound
  linarith [hbound, (Int.fract_lt_one t).le]

/-! ## The two moment kernels -/

/-- The moment kernel of the centred primitive. -/
def burnolCenteredPrimitiveKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  ((burnolCenteredPrimitive y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 2))

/-- The moment kernel of the second primitive. -/
def burnolSecondPrimitiveKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  ((burnolSecondPrimitive y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 3))

theorem norm_burnolCenteredPrimitiveKernel_le {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖burnolCenteredPrimitiveKernel ρ y‖ ≤ 2 * y ^ (-(ρ.re + 2)) := by
  rw [burnolCenteredPrimitiveKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (-(ρ + 2)).re = -(ρ.re + 2) := by
    rw [Complex.neg_re, Complex.add_re]; norm_num
  rw [hre]
  have hpos : (0 : ℝ) < y ^ (-(ρ.re + 2)) := Real.rpow_pos_of_pos hy _
  nlinarith [abs_burnolCenteredPrimitive_le_two y, hpos]

theorem norm_burnolSecondPrimitive_mul_cpow_le {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖((burnolSecondPrimitive y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 2))‖ ≤ 2 * y ^ (-(ρ.re + 2)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (-(ρ + 2)).re = -(ρ.re + 2) := by
    rw [Complex.neg_re, Complex.add_re]; norm_num
  rw [hre]
  have hpos : (0 : ℝ) < y ^ (-(ρ.re + 2)) := Real.rpow_pos_of_pos hy _
  nlinarith [abs_burnolSecondPrimitive_le_two y, hpos]

theorem norm_burnolSecondPrimitiveKernel_le {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    ‖burnolSecondPrimitiveKernel ρ y‖ ≤ 2 * y ^ (-(ρ.re + 3)) := by
  rw [burnolSecondPrimitiveKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (-(ρ + 3)).re = -(ρ.re + 3) := by
    rw [Complex.neg_re, Complex.add_re]; norm_num
  rw [hre]
  have hpos : (0 : ℝ) < y ^ (-(ρ.re + 3)) := Real.rpow_pos_of_pos hy _
  nlinarith [abs_burnolSecondPrimitive_le_two y, hpos]

theorem continuousOn_burnolCenteredPrimitiveKernel (ρ : ℂ) {s : Set ℝ} (hs : ∀ y ∈ s, 0 < y) :
    ContinuousOn (burnolCenteredPrimitiveKernel ρ) s := by
  refine ContinuousOn.mul (Complex.continuous_ofReal.comp
    continuous_burnolCenteredPrimitive).continuousOn ?_
  intro y hy
  exact ((hasDerivAt_burnolRealCpow (hs y hy) (-(ρ + 2))).continuousAt).continuousWithinAt

theorem continuousOn_burnolSecondPrimitiveKernel (ρ : ℂ) {s : Set ℝ} (hs : ∀ y ∈ s, 0 < y) :
    ContinuousOn (burnolSecondPrimitiveKernel ρ) s := by
  refine ContinuousOn.mul (Complex.continuous_ofReal.comp
    continuous_burnolSecondPrimitive).continuousOn ?_
  intro y hy
  exact ((hasDerivAt_burnolRealCpow (hs y hy) (-(ρ + 3))).continuousAt).continuousWithinAt

theorem intervalIntegrable_burnolCenteredPrimitiveKernel {ρ : ℂ} {t T : ℝ} (ht : 0 < t)
    (htT : t ≤ T) : IntervalIntegrable (burnolCenteredPrimitiveKernel ρ) volume t T := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le htT]
  exact continuousOn_burnolCenteredPrimitiveKernel ρ fun y hy => lt_of_lt_of_le ht hy.1

theorem intervalIntegrable_burnolSecondPrimitiveKernel {ρ : ℂ} {t T : ℝ} (ht : 0 < t)
    (htT : t ≤ T) : IntervalIntegrable (burnolSecondPrimitiveKernel ρ) volume t T := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le htT]
  exact continuousOn_burnolSecondPrimitiveKernel ρ fun y hy => lt_of_lt_of_le ht hy.1

theorem integrableOn_burnolCenteredPrimitiveKernel {ρ : ℂ} (hρ : -1 < ρ.re) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (burnolCenteredPrimitiveKernel ρ) (Ioi t) := by
  have hmeas : AEStronglyMeasurable (burnolCenteredPrimitiveKernel ρ)
      (volume.restrict (Ioi t)) :=
    (continuousOn_burnolCenteredPrimitiveKernel ρ
      fun y hy => lt_trans ht hy).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (g := fun y : ℝ => 2 * y ^ (-(ρ.re + 2))) ?_ hmeas ?_
  · exact ((integrableOn_Ioi_rpow_of_lt (by linarith) ht).congr_fun
      (fun _ _ => rfl) measurableSet_Ioi).const_mul 2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact norm_burnolCenteredPrimitiveKernel_le (lt_trans ht hy)

theorem integrableOn_burnolSecondPrimitiveKernel {ρ : ℂ} (hρ : -1 < ρ.re) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (burnolSecondPrimitiveKernel ρ) (Ioi t) := by
  have hmeas : AEStronglyMeasurable (burnolSecondPrimitiveKernel ρ)
      (volume.restrict (Ioi t)) :=
    (continuousOn_burnolSecondPrimitiveKernel ρ
      fun y hy => lt_trans ht hy).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' (g := fun y : ℝ => 2 * y ^ (-(ρ.re + 3))) ?_ hmeas ?_
  · exact ((integrableOn_Ioi_rpow_of_lt (by linarith) ht).congr_fun
      (fun _ _ => rfl) measurableSet_Ioi).const_mul 2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact norm_burnolSecondPrimitiveKernel_le (lt_trans ht hy)

/-! ## The first integration by parts, against the centred primitive -/

theorem hasDerivWithinAt_burnolCenteredByPartsProduct {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    HasDerivWithinAt
      (fun x : ℝ => ((burnolCenteredPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 1)))
      (burnolFractPairKernel ρ y - (ρ + 1) * burnolCenteredPrimitiveKernel ρ y) (Ici y) y := by
  have hP : HasDerivWithinAt (fun x : ℝ => ((burnolCenteredPrimitive x : ℝ) : ℂ))
      ((burnolFractPair y : ℝ) : ℂ) (Ici y) y :=
    (hasDerivWithinAt_burnolCenteredPrimitive y).ofReal_comp
  have hpow : HasDerivWithinAt (fun x : ℝ => (x : ℂ) ^ (-(ρ + 1)))
      (-(ρ + 1) * (y : ℂ) ^ (-(ρ + 1) - 1)) (Ici y) y :=
    (hasDerivAt_burnolRealCpow hy (-(ρ + 1))).hasDerivWithinAt
  have hmul := hP.mul hpow
  refine hmul.congr_deriv ?_
  rw [burnolFractPairKernel, burnolCenteredPrimitiveKernel,
    show -(ρ + 1) - 1 = -(ρ + 2) by ring]
  ring

theorem integral_burnolFractPairKernel_centered_byParts {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (∫ y in t..T, burnolFractPairKernel ρ y) =
      ((burnolCenteredPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 1))
        - ((burnolCenteredPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))
        + (ρ + 1) * ∫ y in t..T, burnolCenteredPrimitiveKernel ρ y := by
  have hint : IntervalIntegrable
      (fun y : ℝ => burnolFractPairKernel ρ y - (ρ + 1) * burnolCenteredPrimitiveKernel ρ y)
      volume t T :=
    (intervalIntegrable_burnolFractPairKernel hρ0 hρ1 ht htT).sub
      ((intervalIntegrable_burnolCenteredPrimitiveKernel ht htT).const_mul _)
  have hcont : ContinuousOn
      (fun x : ℝ => ((burnolCenteredPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 1)))
      (Icc t T) := by
    refine ContinuousOn.mul (Complex.continuous_ofReal.comp
      continuous_burnolCenteredPrimitive).continuousOn ?_
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ht hy.1
    exact ((hasDerivAt_burnolRealCpow hy0 (-(ρ + 1))).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Ioo t T, HasDerivWithinAt
      (fun x : ℝ => ((burnolCenteredPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 1)))
      (burnolFractPairKernel ρ x - (ρ + 1) * burnolCenteredPrimitiveKernel ρ x) (Ioi x) x :=
    fun x hx =>
      (hasDerivWithinAt_burnolCenteredByPartsProduct (lt_trans ht hx.1)).mono Ioi_subset_Ici_self
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le htT hcont hderiv hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_burnolFractPairKernel hρ0 hρ1 ht htT)
    ((intervalIntegrable_burnolCenteredPrimitiveKernel ht htT).const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  linear_combination hftc

/-- **The tail moment of the coboundary, with the centred primitive.**  The boundary term at
infinity vanishes because `P₀` is bounded and `σ + 1 > 0`. -/
theorem integral_burnolFractPairKernel_Ioi_centered {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi t, burnolFractPairKernel ρ y) =
      -(((burnolCenteredPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1)))
        + (ρ + 1) * ∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y := by
  have hlhs : Tendsto (fun T : ℝ => ∫ y in t..T, burnolFractPairKernel ρ y) atTop
      (𝓝 (∫ y in Ioi t, burnolFractPairKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi t
      (integrableOn_burnolFractPairKernel_Ioi hρ0 hρ1 ht) tendsto_id
  have hker : Tendsto (fun T : ℝ => ∫ y in t..T, burnolCenteredPrimitiveKernel ρ y) atTop
      (𝓝 (∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi t
      (integrableOn_burnolCenteredPrimitiveKernel (by linarith) ht) tendsto_id
  have hbdry : Tendsto
      (fun T : ℝ => ((burnolCenteredPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 1))) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto (fun T : ℝ => 2 * T ^ (-(ρ.re + 1))) atTop (𝓝 0) := by
      have h := (_root_.tendsto_rpow_neg_atTop (y := ρ.re + 1) (by linarith)).const_mul (2 : ℝ)
      rw [mul_zero] at h
      exact h
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards with T using norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hT]
      have hre : (-(ρ + 1)).re = -(ρ.re + 1) := by
        rw [Complex.neg_re, Complex.add_re]; norm_num
      rw [hre]
      have hpos : (0 : ℝ) < T ^ (-(ρ.re + 1)) := Real.rpow_pos_of_pos hT _
      nlinarith [abs_burnolCenteredPrimitive_le_two T, hpos]
  have hrhs : Tendsto (fun T : ℝ =>
      ((burnolCenteredPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 1))
        - ((burnolCenteredPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))
        + (ρ + 1) * ∫ y in t..T, burnolCenteredPrimitiveKernel ρ y) atTop
      (𝓝 (0 - ((burnolCenteredPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 1))
        + (ρ + 1) * ∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y)) :=
    (hbdry.sub tendsto_const_nhds).add (hker.const_mul _)
  have heq := tendsto_nhds_unique
    (hlhs.congr' (by
      filter_upwards [eventually_ge_atTop t] with T hT
      exact integral_burnolFractPairKernel_centered_byParts hρ0 hρ1 ht hT)) hrhs
  rw [heq]
  ring

/-! ## The second integration by parts -/

theorem hasDerivAt_burnolSecondByPartsProduct {ρ : ℂ} {y : ℝ} (hy : 0 < y) :
    HasDerivAt
      (fun x : ℝ => ((burnolSecondPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 2)))
      (burnolCenteredPrimitiveKernel ρ y - (ρ + 2) * burnolSecondPrimitiveKernel ρ y) y := by
  have hP : HasDerivAt (fun x : ℝ => ((burnolSecondPrimitive x : ℝ) : ℂ))
      ((burnolCenteredPrimitive y : ℝ) : ℂ) y :=
    (hasDerivAt_burnolSecondPrimitive y).ofReal_comp
  have hpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ (-(ρ + 2)))
      (-(ρ + 2) * (y : ℂ) ^ (-(ρ + 2) - 1)) y :=
    hasDerivAt_burnolRealCpow hy (-(ρ + 2))
  have hmul := hP.mul hpow
  refine hmul.congr_deriv ?_
  rw [burnolCenteredPrimitiveKernel, burnolSecondPrimitiveKernel,
    show -(ρ + 2) - 1 = -(ρ + 3) by ring]
  ring

theorem integral_burnolCenteredPrimitiveKernel_byParts {ρ : ℂ} {t T : ℝ} (ht : 0 < t)
    (htT : t ≤ T) :
    (∫ y in t..T, burnolCenteredPrimitiveKernel ρ y) =
      ((burnolSecondPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 2))
        - ((burnolSecondPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 2))
        + (ρ + 2) * ∫ y in t..T, burnolSecondPrimitiveKernel ρ y := by
  have hint : IntervalIntegrable
      (fun y : ℝ => burnolCenteredPrimitiveKernel ρ y - (ρ + 2) * burnolSecondPrimitiveKernel ρ y)
      volume t T :=
    (intervalIntegrable_burnolCenteredPrimitiveKernel ht htT).sub
      ((intervalIntegrable_burnolSecondPrimitiveKernel ht htT).const_mul _)
  have hderiv : ∀ x ∈ uIcc t T, HasDerivAt
      (fun x : ℝ => ((burnolSecondPrimitive x : ℝ) : ℂ) * (x : ℂ) ^ (-(ρ + 2)))
      (burnolCenteredPrimitiveKernel ρ x - (ρ + 2) * burnolSecondPrimitiveKernel ρ x) x := by
    intro x hx
    rw [Set.uIcc_of_le htT] at hx
    exact hasDerivAt_burnolSecondByPartsProduct (lt_of_lt_of_le ht hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub (intervalIntegrable_burnolCenteredPrimitiveKernel ht htT)
    ((intervalIntegrable_burnolSecondPrimitiveKernel ht htT).const_mul _),
    intervalIntegral.integral_const_mul] at hftc
  linear_combination hftc

/-- **The tail moment of the centred primitive.**  Integration by parts, in the limit. -/
theorem integral_burnolCenteredPrimitiveKernel_Ioi_eq {ρ : ℂ} (hρ : -1 < ρ.re) {t : ℝ}
    (ht : 0 < t) :
    (∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y) =
      -(((burnolSecondPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 2)))
        + (ρ + 2) * ∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y := by
  have hlhs : Tendsto (fun T : ℝ => ∫ y in t..T, burnolCenteredPrimitiveKernel ρ y) atTop
      (𝓝 (∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi t
      (integrableOn_burnolCenteredPrimitiveKernel hρ ht) tendsto_id
  have hker : Tendsto (fun T : ℝ => ∫ y in t..T, burnolSecondPrimitiveKernel ρ y) atTop
      (𝓝 (∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi t
      (integrableOn_burnolSecondPrimitiveKernel hρ ht) tendsto_id
  have hbdry : Tendsto
      (fun T : ℝ => ((burnolSecondPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 2))) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdom : Tendsto (fun T : ℝ => 2 * T ^ (-(ρ.re + 2))) atTop (𝓝 0) := by
      have h := (_root_.tendsto_rpow_neg_atTop (y := ρ.re + 2) (by linarith)).const_mul (2 : ℝ)
      rw [mul_zero] at h
      exact h
    refine squeeze_zero' ?_ ?_ hdom
    · filter_upwards with T using norm_nonneg _
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      exact norm_burnolSecondPrimitive_mul_cpow_le hT
  have hrhs : Tendsto (fun T : ℝ =>
      ((burnolSecondPrimitive T : ℝ) : ℂ) * (T : ℂ) ^ (-(ρ + 2))
        - ((burnolSecondPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 2))
        + (ρ + 2) * ∫ y in t..T, burnolSecondPrimitiveKernel ρ y) atTop
      (𝓝 (0 - ((burnolSecondPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 2))
        + (ρ + 2) * ∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y)) :=
    (hbdry.sub tendsto_const_nhds).add (hker.const_mul _)
  have heq := tendsto_nhds_unique
    (hlhs.congr' (by
      filter_upwards [eventually_ge_atTop t] with T hT
      exact integral_burnolCenteredPrimitiveKernel_byParts ht hT)) hrhs
  rw [heq]
  ring

/-- **The tail moment of the centred primitive is `O(t^{-σ-2})`** — one power better than the
trivial bound, because the second primitive is bounded. -/
theorem norm_integral_burnolCenteredPrimitiveKernel_Ioi_le {ρ : ℂ} (hρ : -1 < ρ.re) {t : ℝ}
    (ht : 0 < t) :
    ‖∫ y in Ioi t, burnolCenteredPrimitiveKernel ρ y‖ ≤
      2 * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-(ρ.re + 2)) := by
  have hbdry : ‖((burnolSecondPrimitive t : ℝ) : ℂ) * (t : ℂ) ^ (-(ρ + 2))‖ ≤
      2 * t ^ (-(ρ.re + 2)) := norm_burnolSecondPrimitive_mul_cpow_le ht
  have hker : ‖∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y‖ ≤
      2 * (t ^ (-(ρ.re + 2)) / (ρ.re + 2)) := by
    have hbound : ∀ᵐ y ∂(volume.restrict (Ioi t)),
        ‖burnolSecondPrimitiveKernel ρ y‖ ≤ 2 * y ^ (-(ρ.re + 3)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact norm_burnolSecondPrimitiveKernel_le (lt_trans ht hy)
    have hintg : IntegrableOn (fun y : ℝ => 2 * y ^ (-(ρ.re + 3))) (Ioi t) :=
      ((integrableOn_Ioi_rpow_of_lt (a := -(ρ.re + 3)) (by linarith) ht).congr_fun
        (fun _ _ => rfl) measurableSet_Ioi).const_mul 2
    have hcmp := MeasureTheory.norm_integral_le_of_norm_le hintg hbound
    rw [MeasureTheory.integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : -(ρ.re + 3) < -1) ht] at hcmp
    have hval : -t ^ (-(ρ.re + 3) + 1) / (-(ρ.re + 3) + 1) = t ^ (-(ρ.re + 2)) / (ρ.re + 2) := by
      rw [show -(ρ.re + 3) + 1 = -(ρ.re + 2) by ring]
      field_simp
    rw [hval] at hcmp
    exact hcmp
  rw [integral_burnolCenteredPrimitiveKernel_Ioi_eq hρ ht]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg]
  have hstep : ‖ρ + 2‖ * ‖∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y‖ ≤
      ‖ρ + 2‖ * (2 * (t ^ (-(ρ.re + 2)) / (ρ.re + 2))) :=
    mul_le_mul_of_nonneg_left hker (norm_nonneg _)
  have hpos : (0 : ℝ) < ρ.re + 2 := by linarith
  have hb2 : ‖(ρ + 2) * ∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y‖ =
      ‖ρ + 2‖ * ‖∫ y in Ioi t, burnolSecondPrimitiveKernel ρ y‖ := norm_mul _ _
  have hexp : 2 * (1 + ‖ρ + 2‖ / (ρ.re + 2)) * t ^ (-(ρ.re + 2)) =
      2 * t ^ (-(ρ.re + 2)) + ‖ρ + 2‖ * (2 * (t ^ (-(ρ.re + 2)) / (ρ.re + 2))) := by
    field_simp
  rw [hexp, hb2]
  linarith [hbdry, hstep]

end RHTower
