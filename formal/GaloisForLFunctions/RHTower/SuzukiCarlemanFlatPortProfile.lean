import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The flat boundary profile `exp (-√L)` and its two ray integrals

The stretched-exponential profile `F(L) = exp(-√L)` is flatter than every inverse-logarithmic
grade yet still decays: on the physical ray `s = e^{-L}` it is square integrable while its
derivative is not, so it lies in the completed boundary class and outside the raw spatial
derivative domain.  This module computes its exact tail integral

`∫_{v > L} exp (-√v) dv = 2 (√L + 1) exp (-√L)`

from the closed antiderivative, and settles the two ray integrals that decide membership.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace RHTower

noncomputable section

/-- The flat boundary profile `F(L) = exp (-√L)`. -/
def flatPortProfile (v : ℝ) : ℝ := Real.exp (-Real.sqrt v)

theorem flatPortProfile_pos (v : ℝ) : 0 < flatPortProfile v := Real.exp_pos _

theorem continuous_flatPortProfile : Continuous flatPortProfile := by
  unfold flatPortProfile
  fun_prop

/-- The closed antiderivative `-2(√v+1) exp(-√v)` of the flat profile. -/
def flatPortAntiderivative (v : ℝ) : ℝ :=
  -2 * (Real.sqrt v + 1) * Real.exp (-Real.sqrt v)

theorem hasDerivAt_flatPortAntiderivative {v : ℝ} (hv : 0 < v) :
    HasDerivAt flatPortAntiderivative (flatPortProfile v) v := by
  have hsq : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt v)) v := Real.hasDerivAt_sqrt (ne_of_gt hv)
  have hspos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-Real.sqrt x))
      (Real.exp (-Real.sqrt v) * (-(1 / (2 * Real.sqrt v)))) v := by
    exact (hsq.neg).exp
  have hlin : HasDerivAt (fun x : ℝ => -2 * (Real.sqrt x + 1))
      (-2 * (1 / (2 * Real.sqrt v))) v := by
    have := (hsq.add_const 1).const_mul (-2 : ℝ)
    simpa using this
  have hmul := hlin.mul hexp
  have hgoal : -2 * (1 / (2 * Real.sqrt v)) * Real.exp (-Real.sqrt v)
      + -2 * (Real.sqrt v + 1) * (Real.exp (-Real.sqrt v) * -(1 / (2 * Real.sqrt v)))
      = flatPortProfile v := by
    rw [flatPortProfile]
    field_simp
    ring
  have hfun : flatPortAntiderivative
      = fun x : ℝ => (-2 * (Real.sqrt x + 1)) * Real.exp (-Real.sqrt x) := by
    funext x
    rw [flatPortAntiderivative]
  rw [hfun, ← hgoal]
  exact hmul

theorem tendsto_flatPortAntiderivative_atTop :
    Tendsto flatPortAntiderivative atTop (𝓝 0) := by
  have hbase : Tendsto (fun y : ℝ => -2 * (y + 1) * Real.exp (-y)) atTop (𝓝 0) := by
    have hpoly : Tendsto (fun y : ℝ => (-2 * y + -2) * Real.exp (-y)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
        simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      have h2 : Tendsto (fun y : ℝ => Real.exp (-y)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
      have := (h1.const_mul (-2 : ℝ)).add (h2.const_mul (-2 : ℝ))
      simpa using this.congr (fun y => by ring)
    exact hpoly.congr fun y => by ring
  have hsqrt : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  have := hbase.comp hsqrt
  refine this.congr fun v => ?_
  rw [Function.comp_apply, flatPortAntiderivative]

theorem intervalIntegrable_flatPortProfile (a b : ℝ) :
    IntervalIntegrable flatPortProfile volume a b :=
  continuous_flatPortProfile.intervalIntegrable a b

/-- The flat profile is integrable on every ray. -/
theorem integrableOn_flatPortProfile (L : ℝ) (hL : 0 < L) :
    IntegrableOn flatPortProfile (Ioi L) volume := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := flatPortAntiderivative) (l := 0)
    (hasDerivAt_flatPortAntiderivative hL).continuousAt.continuousWithinAt
    (fun x hx => hasDerivAt_flatPortAntiderivative (lt_trans hL hx))
    (fun x _ => (flatPortProfile_pos x).le) tendsto_flatPortAntiderivative_atTop

/-- **`(17)`: the exact flat tail integral.** -/
theorem integral_Ioi_flatPortProfile {L : ℝ} (hL : 0 < L) :
    (∫ v in Ioi L, flatPortProfile v)
      = 2 * (Real.sqrt L + 1) * Real.exp (-Real.sqrt L) := by
  have hderiv : ∀ x ∈ Ioi L, HasDerivAt flatPortAntiderivative (flatPortProfile x) x :=
    fun x hx => hasDerivAt_flatPortAntiderivative (lt_trans hL hx)
  have hint : IntegrableOn flatPortProfile (Ioi L) volume := integrableOn_flatPortProfile L hL
  have := integral_Ioi_of_hasDerivAt_of_tendsto
    (hasDerivAt_flatPortAntiderivative hL).continuousAt.continuousWithinAt hderiv hint
    tendsto_flatPortAntiderivative_atTop
  rw [this, flatPortAntiderivative]
  ring

/-- **`(3)`: the flat profile beats every square-root grade.** -/
theorem tendsto_sqrt_mul_flatPortProfile :
    Tendsto (fun L : ℝ => Real.sqrt L * flatPortProfile L) atTop (𝓝 0) := by
  have hbase : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have := hbase.comp Real.tendsto_sqrt_atTop
  refine this.congr fun L => ?_
  rw [Function.comp_apply, flatPortProfile]

/-- A nonnegative function that grows without bound is not integrable on a ray. -/
theorem not_integrableOn_Ioi_of_tendsto_atTop {f : ℝ → ℝ}
    (hf : Tendsto f atTop atTop) (c : ℝ) : ¬ IntegrableOn f (Ioi c) := by
  intro hint
  obtain ⟨N, hN⟩ := (hf.eventually_ge_atTop 1).exists_forall_of_atTop
  set M : ℝ := max N c with hM
  have hsub : IntegrableOn f (Ioi M) volume := hint.mono_set (Ioi_subset_Ioi (le_max_right N c))
  have hle : ∀ x ∈ Ioi M, (1 : ℝ≥0∞) ≤ ‖f x‖ₑ := by
    intro x hx
    have hx1 : 1 ≤ f x := hN x (le_trans (le_max_left N c) (le_of_lt hx))
    have : (1 : ℝ) ≤ ‖f x‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact hx1
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal ‖f x‖ := ENNReal.ofReal_le_ofReal this
      _ = ‖f x‖ₑ := ofReal_norm _
  have hvol : volume (Ioi M) = ⊤ := by
    rw [Real.volume_Ioi]
  have hlint : (∫⁻ x in Ioi M, ‖f x‖ₑ) = ⊤ := by
    have hmono : (∫⁻ _x in Ioi M, (1 : ℝ≥0∞)) ≤ ∫⁻ x in Ioi M, ‖f x‖ₑ := by
      apply setLIntegral_mono' measurableSet_Ioi
      exact hle
    rw [setLIntegral_one, hvol] at hmono
    exact top_le_iff.mp hmono
  have := hsub.2
  rw [HasFiniteIntegral, hlint] at this
  exact absurd this (by simp)

end

end RHTower
