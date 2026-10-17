import GaloisForLFunctions.BiScaleUncertainty.HyperbolicPolarBalanceAndLevySinhFunctional
import GaloisForLFunctions.RHTower.EvenSectorLevyKreinRigidity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Folded-Collar Integral Bounds & Resolution of the Single-Point Interpolation Obstruction

In `GaloisForLFunctions.RHTower.EvenSectorSmoothBlindInterpolationObstruction`, it was shown that
imposing `h(log 2) = 0` on a smooth even polar autocorrelation `h = autocorr f` does **not** force
a universal positive lower bound on `h(0) - h(x)` at every individual interior point `x ∈ (0, log 2)`
in isolation: at the non-dyadic point `x = 4 log 2 / 5`, a pulse train `g_N` with spacing
`a = 4 log 2 / 5` (modeling `cos(5 π x / (2 log 2))`) satisfies `h_N(log 2) = 0` while
`(h_N(0) - h_N(4 log 2 / 5)) / h_N(0) = 1 / (N + 1) → 0`.

This module proves **why** that single-point phenomenon occurs and **how Bi-Scale Uncertainty
Theory resolves it unconditionally for the Lévy–sinh integral**:

1. **Why the Single-Point Bound Fails at Non-Dyadic Points (`autocorr_reflected_collar_sphere_le`):**
   When `h(t₁) = 0`, the exact constraint on `(h(x), h(t₁ - x))` is the **Euclidean Sphere Law**
   `h(x)^2 + h(t₁ - x)^2 ≤ h(0)^2`.
   At the midpoint `x = t₁ / 2` (and along all dyadic/harmonic subdivisions `t₁ / m`), a single
   point is coupled to itself, forcing `h(0) - h(t₁ / m) ≥ h(0) / m^2`. At an asymmetric point
   `x ≠ t₁ / 2` (such as `x = 4 log 2 / 5`), the sphere `u^2 + v^2 ≤ h(0)^2` contains the corner
   `(h(x), h(t₁ - x)) = (h(0), 0)`: `h(x)` can approach `h(0)` at `x = 4 log 2 / 5`, **but only by
   forcing `h(t₁ - x) = h(log 2 / 5)` to approach `0`**!
2. **Universal Pointwise Positivity of the Reflected-Collar Pair
   (`autocorr_weighted_reflected_pair_ge_sphere`, `autocorr_weighted_reflected_pair_ge_min`):**
   Although `h(0) - h(x)` can be small at `x` alone, the **weighted reflected pair** at `(x, t₁ - x)`
   satisfies, for all `x ∈ ℝ` and all `w_L, w_R ≥ 0`:
   `w_L (h(0) - h(x)) + w_R (h(0) - h(t₁ - x))`
   `≥ (w_L + w_R - √(w_L^2 + w_R^2)) h(0) ≥ (2 - √2) min(w_L, w_R) h(0)`.
3. **Unconditional Folded-Interval Lower Bound on the Bi-Scale Lévy Energy
   (`biScaleLevyEnergy_ge_folded_collar_integral`,
   `RealSmoothEvenPolarTestFn.weilArchRe_ge_folded_collar_of_log_two_blind`):**
   Because the integral `∫ x in Ioi 0, (h(0) - h(x)) w_arch(x)` integrates over **both**
   `x ∈ (a, t₁ / 2)` and `t₁ - x ∈ (t₁ / 2, t₁ - a)`, folding the interval `[a, t₁ - a]` around the
   midpoint `t₁ / 2` pairs every `x` with `t₁ - x`, yielding an unconditional, strictly positive,
   derivative-free lower bound on `biScaleLevyEnergy f` for every test function with `h(t₁) = 0`.
-/

open Complex MeasureTheory Set Filter Topology intervalIntegral
open scoped Real
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {f : ℝ → ℝ}

/-! ### 1. Pointwise Weighted Reflected-Collar Lower Bounds -/

/-- Elementary algebraic inequality: for all `a, b ≥ 0`,
`(2 - √2) * min a b ≤ a + b - √(a^2 + b^2)`. -/
theorem two_sub_sqrt_two_mul_min_le_add_sub_sqrt_sq_add_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (2 - Real.sqrt 2) * min a b ≤ a + b - Real.sqrt (a ^ 2 + b ^ 2) := by
  set m := min a b
  have hm0 : 0 ≤ m := le_min ha hb
  have hma : m ≤ a := min_le_left a b
  have hmb : m ≤ b := min_le_right a b
  set u := a - m
  set v := b - m
  have hu : 0 ≤ u := sub_nonneg.mpr hma
  have hv : 0 ≤ v := sub_nonneg.mpr hmb
  have hbound : a ^ 2 + b ^ 2 ≤ (Real.sqrt 2 * m + u + v) ^ 2 := by
    have hsqrt2 : 1 ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt one_le_two
    have hexp : (Real.sqrt 2 * m + u + v) ^ 2 - (a ^ 2 + b ^ 2) =
        2 * (Real.sqrt 2 - 1) * m * (u + v) + 2 * u * v := by
      have hm2 : (Real.sqrt 2 * m) ^ 2 = 2 * m ^ 2 := by
        rw [mul_pow, Real.sq_sqrt zero_le_two]
      calc (Real.sqrt 2 * m + u + v) ^ 2 - (a ^ 2 + b ^ 2)
          = (Real.sqrt 2 * m) ^ 2 + 2 * (Real.sqrt 2 * m) * (u + v) + (u + v) ^ 2 -
              ((m + u) ^ 2 + (m + v) ^ 2) := by
            simp only [u, v]; ring
        _ = 2 * m ^ 2 + 2 * (Real.sqrt 2 * m) * (u + v) + (u + v) ^ 2 -
              ((m + u) ^ 2 + (m + v) ^ 2) := by rw [hm2]
        _ = 2 * (Real.sqrt 2 - 1) * m * (u + v) + 2 * u * v := by ring
    have hnn : 0 ≤ 2 * (Real.sqrt 2 - 1) * m * (u + v) + 2 * u * v := by
      have : 0 ≤ Real.sqrt 2 - 1 := sub_nonneg.mpr hsqrt2
      positivity
    linarith
  have hpos : 0 ≤ Real.sqrt 2 * m + u + v := by positivity
  have hsqrt := Real.sqrt_le_sqrt hbound
  rw [Real.sqrt_sq hpos] at hsqrt
  have hab : a + b = 2 * m + u + v := by simp only [u, v]; ring
  linarith

/-- **Pointwise Weighted Reflected-Collar Sphere Bound:**
If `h(t₁) = 0`, then for any weights `w_L, w_R : ℝ` and any `x ∈ ℝ`,
`(w_L + w_R - √(w_L^2 + w_R^2)) * h(0)`
`≤ w_L * (h(0) - h(x)) + w_R * (h(0) - h(t₁ - x))`. -/
theorem autocorr_weighted_reflected_pair_ge_sphere (hfc : HasCompactSupport f) (hf : Continuous f)
    {t₁ : ℝ} (ht₁ : autocorr f t₁ = 0) (w_L w_R x : ℝ) :
    (w_L + w_R - Real.sqrt (w_L ^ 2 + w_R ^ 2)) * autocorr f 0 ≤
      w_L * (autocorr f 0 - autocorr f x) + w_R * (autocorr f 0 - autocorr f (t₁ - x)) := by
  have hsph := autocorr_reflected_collar_sphere_le hfc hf ht₁ x
  have hlev := origin_singularity_leverage_sphere_bound ({0} : Finset ℕ) w_L
    (fun _ => w_R) (fun _ => autocorr f (t₁ - x)) (autocorr f x) (autocorr f 0)
    (autocorr_zero_nonneg f) (by simpa using hsph)
  simpa using hlev

/-- **Pointwise Weighted Reflected-Collar Minimum-Weight Bound:**
If `h(t₁) = 0` and `w_L, w_R ≥ 0`, then for every `x ∈ ℝ`,
`(2 - √2) * min w_L w_R * h(0) ≤ w_L * (h(0) - h(x)) + w_R * (h(0) - h(t₁ - x))`. -/
theorem autocorr_weighted_reflected_pair_ge_min (hfc : HasCompactSupport f) (hf : Continuous f)
    {t₁ : ℝ} (ht₁ : autocorr f t₁ = 0) {w_L w_R : ℝ} (hwL : 0 ≤ w_L) (hwR : 0 ≤ w_R) (x : ℝ) :
    (2 - Real.sqrt 2) * min w_L w_R * autocorr f 0 ≤
      w_L * (autocorr f 0 - autocorr f x) + w_R * (autocorr f 0 - autocorr f (t₁ - x)) := by
  have h1 := mul_le_mul_of_nonneg_right
    (two_sub_sqrt_two_mul_min_le_add_sub_sqrt_sq_add_sq hwL hwR) (autocorr_zero_nonneg f)
  exact h1.trans (autocorr_weighted_reflected_pair_ge_sphere hfc hf ht₁ w_L w_R x)

/-! ### 2. Folded-Interval Identity and Unconditional Integral Lower Bounds -/

/-- Folding an interval-integrable function `F` around the midpoint `t₁ / 2` on `[a, t₁ - a]`:
`∫ x in a..(t₁ - a), F x = ∫ x in a..(t₁ / 2), (F x + F (t₁ - x))`. -/
theorem intervalIntegral_fold_midpoint {F : ℝ → ℝ} (a t₁ : ℝ)
    (hF1 : IntervalIntegrable F volume a (t₁ / 2))
    (hF2 : IntervalIntegrable F volume (t₁ / 2) (t₁ - a)) :
    (∫ x in a..(t₁ - a), F x) = ∫ x in a..(t₁ / 2), (F x + F (t₁ - x)) := by
  rw [← integral_add_adjacent_intervals hF1 hF2]
  have hrefl : (∫ x in (t₁ / 2)..(t₁ - a), F x) = ∫ x in a..(t₁ / 2), F (t₁ - x) := by
    have hcomp := integral_comp_sub_left F t₁ (a := a) (b := t₁ / 2)
    have h1 : t₁ - (t₁ / 2) = t₁ / 2 := by ring
    rw [h1] at hcomp
    exact hcomp.symm
  rw [hrefl]
  have hF2' : IntervalIntegrable (fun x => F (t₁ - x)) volume a (t₁ / 2) := by
    have := hF2.comp_sub_left t₁
    rw [show t₁ - (t₁ - a) = a by ring, show t₁ - t₁ / 2 = t₁ / 2 by ring] at this
    exact this.symm
  exact (integral_add hF1 hF2').symm

/-- The folded collar leverage kernel for a weight `w` and node `t₁`:
`K_{w, t₁}(x) = w(x) + w(t₁ - x) - √(w(x)^2 + w(t₁ - x)^2)`. -/
def foldedCollarKernel (w : ℝ → ℝ) (t₁ x : ℝ) : ℝ :=
  w x + w (t₁ - x) - Real.sqrt (w x ^ 2 + w (t₁ - x) ^ 2)

/-- The folded collar leverage constant on `[a, t₁ / 2]` for the archimedean Lévy weight:
`C_fold(a, t₁) = ∫ x in a..(t₁ / 2), foldedCollarKernel archLevySinhWeight t₁ x`. -/
def archFoldedCollarConstant (a t₁ : ℝ) : ℝ :=
  ∫ x in a..(t₁ / 2), foldedCollarKernel archLevySinhWeight t₁ x

/-- Pointwise lower bound on `foldedCollarKernel w t₁ x`:
`(2 - √2) * min (w x) (w (t₁ - x)) ≤ foldedCollarKernel w t₁ x` when `w x, w (t₁ - x) ≥ 0`. -/
theorem foldedCollarKernel_ge_two_sub_sqrt_two_mul_min {w : ℝ → ℝ} {t₁ x : ℝ}
    (hx : 0 ≤ w x) (hxt : 0 ≤ w (t₁ - x)) :
    (2 - Real.sqrt 2) * min (w x) (w (t₁ - x)) ≤ foldedCollarKernel w t₁ x :=
  two_sub_sqrt_two_mul_min_le_add_sub_sqrt_sq_add_sq hx hxt

/-- Continuity of `archLevySinhWeight` on any subset of `(0, ∞)`. -/
theorem continuousOn_archLevySinhWeight {s : Set ℝ} (hs : ∀ x ∈ s, 0 < x) :
    ContinuousOn archLevySinhWeight s := by
  unfold archLevySinhWeight
  exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
    Real.continuous_sinh.continuousOn fun x hx => (Real.sinh_pos_iff.mpr (hs x hx)).ne'

/-- **General Folded-Collar Interval Integral Lower Bound:**
Let `w : ℝ → ℝ` be continuous on `[a, t₁ - a]` with `a ≤ t₁ / 2`, and suppose `autocorr f` is
continuous with `autocorr f t₁ = 0`. Then
`(∫ x in a..(t₁ / 2), foldedCollarKernel w t₁ x) * h(0)`
`≤ ∫ x in a..(t₁ - a), (h(0) - h(x)) * w x`. -/
theorem integral_autocorr_sub_mul_ge_folded_sphere
    (hfc : HasCompactSupport f) (hf : Continuous f) (hhc : Continuous (autocorr f))
    {t₁ a : ℝ} (ht₁ : autocorr f t₁ = 0) (ha : a ≤ t₁ / 2)
    {w : ℝ → ℝ} (hwc : ContinuousOn w (Icc a (t₁ - a))) :
    (∫ x in a..(t₁ / 2), foldedCollarKernel w t₁ x) * autocorr f 0 ≤
      ∫ x in a..(t₁ - a), (autocorr f 0 - autocorr f x) * w x := by
  set F : ℝ → ℝ := fun x => (autocorr f 0 - autocorr f x) * w x
  have hFc : ContinuousOn F (Icc a (t₁ - a)) :=
    (continuousOn_const.sub hhc.continuousOn).mul hwc
  have hsub1 : uIcc a (t₁ / 2) ⊆ Icc a (t₁ - a) := by
    rw [uIcc_of_le ha]
    intro x hx
    exact ⟨hx.1, hx.2.trans (by linarith)⟩
  have hsub2 : uIcc (t₁ / 2) (t₁ - a) ⊆ Icc a (t₁ - a) := by
    rw [uIcc_of_le (by linarith)]
    intro x hx
    exact ⟨(by linarith : a ≤ t₁ / 2).trans hx.1, hx.2⟩
  have hF1 : IntervalIntegrable F volume a (t₁ / 2) :=
    (hFc.mono hsub1).intervalIntegrable
  have hF2 : IntervalIntegrable F volume (t₁ / 2) (t₁ - a) :=
    (hFc.mono hsub2).intervalIntegrable
  rw [intervalIntegral_fold_midpoint a t₁ hF1 hF2, ← intervalIntegral.integral_mul_const]
  have hKc : ContinuousOn (fun x => foldedCollarKernel w t₁ x * autocorr f 0) (uIcc a (t₁ / 2)) := by
    have hw1 : ContinuousOn w (uIcc a (t₁ / 2)) := hwc.mono hsub1
    have hw2 : ContinuousOn (fun x => w (t₁ - x)) (uIcc a (t₁ / 2)) := by
      refine hwc.comp (continuous_const.sub continuous_id).continuousOn ?_
      intro x hx
      rw [uIcc_of_le ha] at hx
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    unfold foldedCollarKernel
    exact ((hw1.add hw2).sub
      (Real.continuous_sqrt.comp_continuousOn ((hw1.pow 2).add (hw2.pow 2)))).mul continuousOn_const
  have hFsum : IntervalIntegrable (fun x => F x + F (t₁ - x)) volume a (t₁ / 2) := by
    refine hF1.add ?_
    have := hF2.comp_sub_left t₁
    rw [show t₁ - (t₁ - a) = a by ring, show t₁ - t₁ / 2 = t₁ / 2 by ring] at this
    exact this.symm
  refine integral_mono_on ha hKc.intervalIntegrable hFsum fun x hx => ?_
  have hpt := autocorr_weighted_reflected_pair_ge_sphere hfc hf ht₁ (w x) (w (t₁ - x)) x
  simpa [F, foldedCollarKernel, mul_comm] using hpt

/-- **Unconditional Folded-Collar Lower Bound on the Bi-Scale Lévy Energy:**
For any `f ∈ C²_c(ℝ)` with `autocorr f t₁ = 0` and any `0 < a ≤ t₁ / 2`,
`archFoldedCollarConstant a t₁ * autocorr f 0 ≤ biScaleLevyEnergy f`. -/
theorem biScaleLevyEnergy_ge_folded_collar_integral
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {t₁ a : ℝ} (ht₁ : autocorr f t₁ = 0) (ha0 : 0 < a) (ha : a ≤ t₁ / 2) :
    archFoldedCollarConstant a t₁ * autocorr f 0 ≤ biScaleLevyEnergy f := by
  have hhc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hwc : ContinuousOn archLevySinhWeight (Icc a (t₁ - a)) :=
    continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le ha0 hx.1
  have hfold := integral_autocorr_sub_mul_ge_folded_sphere hfc hf.continuous hhc ht₁ ha hwc
  refine hfold.trans ?_
  rw [intervalIntegral.integral_of_le (by linarith : a ≤ t₁ - a)]
  unfold biScaleLevyEnergy
  refine setIntegral_mono_set (integrableOn_biScaleLevyIntegrand hf hfc) ?_ ?_
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    exact mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le
  · refine Eventually.of_forall fun x hx => ?_
    exact lt_of_lt_of_le ha0 hx.1.le

/-- **Strict Positivity of the Archimedean Folded-Collar Constant:**
For any `0 < a < t₁ / 2`, `0 < archFoldedCollarConstant a t₁`. -/
theorem archFoldedCollarConstant_pos {a t₁ : ℝ} (ha0 : 0 < a) (ha : a < t₁ / 2) :
    0 < archFoldedCollarConstant a t₁ := by
  unfold archFoldedCollarConstant
  have hwc : ContinuousOn archLevySinhWeight (Icc a (t₁ - a)) :=
    continuousOn_archLevySinhWeight fun x hx => lt_of_lt_of_le ha0 hx.1
  have hsub1 : uIcc a (t₁ / 2) ⊆ Icc a (t₁ - a) := by
    rw [uIcc_of_le ha.le]
    intro x hx
    exact ⟨hx.1, hx.2.trans (by linarith)⟩
  have hw1 : ContinuousOn archLevySinhWeight (uIcc a (t₁ / 2)) := hwc.mono hsub1
  have hw2 : ContinuousOn (fun x => archLevySinhWeight (t₁ - x)) (uIcc a (t₁ / 2)) := by
    refine hwc.comp (continuous_const.sub continuous_id).continuousOn ?_
    intro x hx
    rw [uIcc_of_le ha.le] at hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hKc : ContinuousOn (foldedCollarKernel archLevySinhWeight t₁) (uIcc a (t₁ / 2)) := by
    unfold foldedCollarKernel
    exact (hw1.add hw2).sub
      (Real.continuous_sqrt.comp_continuousOn ((hw1.pow 2).add (hw2.pow 2)))
  have hmin_c : ContinuousOn
      (fun x => (2 - Real.sqrt 2) * min (archLevySinhWeight x) (archLevySinhWeight (t₁ - x)))
      (uIcc a (t₁ / 2)) :=
    continuousOn_const.mul (hw1.inf hw2)
  have hmono : (∫ x in a..(t₁ / 2),
      (2 - Real.sqrt 2) * min (archLevySinhWeight x) (archLevySinhWeight (t₁ - x))) ≤
      ∫ x in a..(t₁ / 2), foldedCollarKernel archLevySinhWeight t₁ x := by
    refine integral_mono_on ha.le hmin_c.intervalIntegrable hKc.intervalIntegrable fun x hx => ?_
    have hx_pos : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hxt_pos : 0 < t₁ - x := by linarith [hx.2]
    exact foldedCollarKernel_ge_two_sub_sqrt_two_mul_min
      (archLevySinhWeight_pos hx_pos).le (archLevySinhWeight_pos hxt_pos).le
  refine lt_of_lt_of_le ?_ hmono
  have hpos_on : ∀ x ∈ Icc a (t₁ / 2),
      0 < (2 - Real.sqrt 2) * min (archLevySinhWeight x) (archLevySinhWeight (t₁ - x)) := by
    intro x hx
    have h2 : Real.sqrt 2 < 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hx_pos : 0 < x := lt_of_lt_of_le ha0 hx.1
    have hxt_pos : 0 < t₁ - x := by linarith [hx.2]
    exact mul_pos (by linarith) (lt_min (archLevySinhWeight_pos hx_pos) (archLevySinhWeight_pos hxt_pos))
  obtain ⟨x₀, hx₀_mem, hx₀_min⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr ha.le) (by rwa [uIcc_of_le ha.le] at hmin_c)
  have hc0 : 0 < (2 - Real.sqrt 2) * min (archLevySinhWeight x₀) (archLevySinhWeight (t₁ - x₀)) :=
    hpos_on x₀ hx₀_mem
  have hconst_le : (∫ x in a..(t₁ / 2),
      (2 - Real.sqrt 2) * min (archLevySinhWeight x₀) (archLevySinhWeight (t₁ - x₀))) ≤
      ∫ x in a..(t₁ / 2),
        (2 - Real.sqrt 2) * min (archLevySinhWeight x) (archLevySinhWeight (t₁ - x)) :=
    integral_mono_on ha.le intervalIntegrable_const hmin_c.intervalIntegrable fun x hx => hx₀_min hx
  refine lt_of_lt_of_le ?_ hconst_le
  rw [intervalIntegral.integral_const, smul_eq_mul]
  exact mul_pos (sub_pos.mpr ha) hc0

/-- **Resolution of the Single-Point Obstruction for Smooth EWU Tests (`RealSmoothEvenPolarTestFn`):**
Every real smooth even polar test `g : RealSmoothEvenPolarTestFn` that is blind at `log 2`
(`EF.weilTest g g (Real.log 2) = 0`) satisfies the unconditional folded-collar archimedean lower
bound, for every `0 < a ≤ Real.log 2 / 2`:
`(EF.gammaBracket 0 + archFoldedCollarConstant a (Real.log 2)) * (EF.weilTest g g 0).re`
`≤ weilArchRe (EF.weilTest g g)`,
with `0 < archFoldedCollarConstant a (Real.log 2)` whenever `0 < a < Real.log 2 / 2`. -/
theorem RealSmoothEvenPolarTestFn.weilArchRe_ge_folded_collar_of_log_two_blind
    (g : RealSmoothEvenPolarTestFn)
    (hblind : EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log 2) = 0)
    {a : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.log 2 / 2) :
    (EF.gammaBracket 0 + archFoldedCollarConstant a (Real.log 2)) *
      (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) := by
  have hlev := g.weilArchRe_eq_levy
  have hautocorr : ∀ x, (EF.weilTest g.1.1.1.1 g.1.1.1.1 x).re = autocorr g.toRealEvenPolar.source x :=
    fun x => (g.toRealEvenPolar.autocorr_eq x).symm
  have ht₁ : autocorr g.toRealEvenPolar.source (Real.log 2) = 0 := by
    rw [← hautocorr (Real.log 2), hblind, Complex.zero_re]
  have hbound := biScaleLevyEnergy_ge_folded_collar_integral
    g.toRealEvenPolar.contDiff_source g.toRealEvenPolar.hasCompactSupport_source ht₁ ha0 ha
  have hint_eq : (∫ x in Ioi 0, ((EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re -
      (EF.weilTest g.1.1.1.1 g.1.1.1.1 x).re) * (Real.exp (x / 2) / Real.sinh x)) =
      biScaleLevyEnergy g.toRealEvenPolar.source := by
    unfold biScaleLevyEnergy archLevySinhWeight
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [hautocorr 0, hautocorr x]
  rw [hlev, hint_eq, hautocorr 0]
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
