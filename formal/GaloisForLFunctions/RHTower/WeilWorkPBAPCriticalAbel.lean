import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Signed cumulative sums and their Laplace transform

Absolute convergence is proved before exchanging series and integral. No sign
condition is imposed on the arithmetic coefficients or cumulative sums.
-/

open MeasureTheory Filter Topology Set Real
open scoped ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- A signed atomic cumulative sum. -/
def signedCumulative {ι : Type*} (w p : ι → ℝ) (t : ℝ) : ℝ :=
  ∑' i, if p i ≤ t then w i else 0

/-- Elementary Abel/Fubini identity, with absolute convergence as its exact analytic condition. -/
theorem integral_signedCumulative_exp {ι : Type*} [Countable ι] (w p : ι → ℝ)
    {s : ℝ} (hs : 0 < s) (habs : Summable fun i => |w i| * exp (-s * p i)) :
    ∫ t : ℝ, signedCumulative w p t * exp (-s*t) =
      (∑' i, w i * exp (-s*p i)) / s := by
  classical
  let F : ι → ℝ → ℝ := fun i => (Ici (p i)).indicator (fun t => w i * exp (-s*t))
  have hi : ∀ i, Integrable (F i) := fun i =>
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      ((exp_neg_integrableOn_Ioi (p i) hs).const_mul (w i))).integrable_indicator measurableSet_Ici
  have hv : ∀ i, ∫ t : ℝ, F i t = w i * exp (-s*p i) / s := by
    intro i
    dsimp only [F]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hs)]
    ring
  have hn : ∀ i, ∫ t : ℝ, ‖F i t‖ = |w i| * exp (-s*p i) / s := by
    intro i
    have heq : (fun t => ‖F i t‖) =
        (Ici (p i)).indicator (fun t => |w i| * exp (-s*t)) := by
      funext t
      by_cases ht : p i ≤ t
      · simp [F, ht, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      · simp [F, ht]
    rw [heq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hs)]
    ring
  have hsum : Summable fun i => ∫ t : ℝ, ‖F i t‖ := by
    simp_rw [hn]
    exact habs.div_const s
  have hpoint : ∀ t, signedCumulative w p t * exp (-s*t) = ∑' i, F i t := by
    intro t
    rw [signedCumulative, ← tsum_mul_right]
    apply tsum_congr
    intro i
    by_cases ht : p i ≤ t <;> simp [F, ht]
  simp_rw [hpoint]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  simp_rw [hv]
  exact tsum_div_const

/-- Exact polynomial Laplace moment used by the sharp density ceiling. -/
theorem integral_sq_exp_neg {s : ℝ} (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), t^2 * exp (-s*t) = 2 / s^3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (by norm_num) hs
  norm_num [Real.Gamma_nat_eq_factorial, Real.rpow_natCast, neg_mul] at h
  have he : (fun t : ℝ => t^2 * exp (-s*t)) =
      fun t => t^2 * exp (-(s*t)) := by
    funext t
    rw [neg_mul]
  rw [he, h]
  simp only [div_eq_mul_inv]
  ring

/-- An upper quadratic ceiling transfers to the Laplace transform even for signed sums. -/
theorem signedCumulative_laplace_ceiling {ι : Type*} [Countable ι] (w p : ι → ℝ)
    {s A M : ℝ} (hs : 0 < s) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hp : ∀ i, 0 ≤ p i) (habs : Summable fun i => |w i| * exp (-s*p i))
    (hupper : ∀ t : ℝ, 0 ≤ t → signedCumulative w p t ≤ A*t^2+M) :
    (∑' i, w i * exp (-s*p i)) / s ≤ A * (2/s^3) + M/s := by
  classical
  let U : ℝ → ℝ := (Ici (0:ℝ)).indicator (fun t => (A*t^2+M)*exp (-s*t))
  have hi2 : IntegrableOn (fun t : ℝ => t^2*exp (-s*t)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_sq_exp_neg hs]
    positivity
  have hi0 := exp_neg_integrableOn_Ioi 0 hs
  have hpoly : (fun t : ℝ => (A*t^2+M)*exp (-s*t)) =
      fun t => A*(t^2*exp (-s*t))+M*exp (-s*t) := by funext t; ring
  have hiU0 : IntegrableOn (fun t : ℝ => (A*t^2+M)*exp (-s*t)) (Ioi 0) := by
    rw [hpoly]
    exact (hi2.const_mul A).add (hi0.const_mul M)
  have hiU : Integrable U :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hiU0).integrable_indicator measurableSet_Ici
  have hU : ∫ t, U t = A*(2/s^3)+M/s := by
    dsimp only [U]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, hpoly,
      integral_add (hi2.const_mul A) (hi0.const_mul M), integral_const_mul,
      integral_const_mul, integral_sq_exp_neg hs, integral_exp_mul_Ioi (neg_neg_of_pos hs) 0]
    simp only [mul_zero, exp_zero]
    ring
  have hpoint : ∀ t, signedCumulative w p t * exp (-s*t) ≤ U t := by
    intro t
    by_cases ht : 0 ≤ t
    · dsimp only [U]
      rw [Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)]
      exact mul_le_mul_of_nonneg_right (hupper t ht) (exp_pos _).le
    · have hz : signedCumulative w p t = 0 := by
        have hn (i : ι) : ¬p i ≤ t := not_le.mpr (lt_of_lt_of_le (lt_of_not_ge ht) (hp i))
        simp [signedCumulative, hn]
      simp [U, ht, hz]
  rw [← integral_signedCumulative_exp w p hs habs, ← hU]
  by_cases hi : Integrable (fun t => signedCumulative w p t * exp (-s*t))
  · exact integral_mono hi hiU hpoint
  · rw [integral_undef hi]
    apply integral_nonneg
    intro t
    by_cases ht : 0 ≤ t
    · dsimp only [U]
      rw [Set.indicator_of_mem (show t ∈ Ici (0:ℝ) from ht)]
      positivity
    · simp [U, ht]

end RHTower.WeilWorkPBAP
