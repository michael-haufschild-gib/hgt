import GaloisForLFunctions.ExceptionalLayerTheory.TheTwoIntervalRadiusControlsEachSquaredPrimeIncrement
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRayleighFloor

/-!
# Sign control for the ordinary-prime increment

A unit average makes the prime count continuous at a cost of at most one
prime's logarithm. A continuous increment cannot reverse sign on a part of
a wave where its squared amplitude stays above the squared-error bound.
-/

noncomputable section
open Filter Topology MeasureTheory Set
open GaloisForLFunctions.ZeroConfigurationGeometry
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def unitAverageTheta (x : ℝ) := ∫ y in x..x+1, Chebyshev.theta y

private theorem continuous_unitAverageTheta : Continuous unitAverageTheta := by
  let P := fun x : ℝ => ∫ y in (0:ℝ)..x, Chebyshev.theta y
  have hi (a b : ℝ) : IntervalIntegrable Chebyshev.theta volume a b :=
    Chebyshev.theta_mono.intervalIntegrable
  have hp : Continuous P := intervalIntegral.continuous_primitive hi 0
  have he (x : ℝ) : unitAverageTheta x = P (x+1)-P x := by
    have ha := intervalIntegral.integral_add_adjacent_intervals (hi 0 x) (hi x (x+1))
    exact eq_sub_of_add_eq' ha
  rw [funext he]
  exact (hp.comp (continuous_id.add continuous_const)).sub hp

private theorem abs_unitAverageTheta_sub_theta {x : ℝ} (hx : 0 ≤ x) :
    |unitAverageTheta x - Chebyshev.theta x| ≤ Real.log (x+1) := by
  have hxx : x ≤ x+1 := le_add_of_nonneg_right zero_le_one
  have hi : IntervalIntegrable Chebyshev.theta volume x (x+1) :=
    Chebyshev.theta_mono.intervalIntegrable
  have hlo := intervalIntegral.integral_mono_on hxx
    (intervalIntegrable_const (c := Chebyshev.theta x)) hi
    (fun y hy => Chebyshev.theta_mono hy.1)
  have hhi := intervalIntegral.integral_mono_on hxx hi
    (intervalIntegrable_const (c := Chebyshev.theta (x+1)))
    (fun y hy => Chebyshev.theta_mono hy.2)
  simp only [intervalIntegral.integral_const,add_sub_cancel_left,one_smul] at hlo hhi
  rw [unitAverageTheta, abs_of_nonneg (sub_nonneg.mpr hlo)]
  refine (sub_le_sub_right hhi _).trans ?_
  rw [RHTower.Sieve.theta_sub_eq_sum_Ioc hxx, Nat.floor_add_one hx,
    Nat.Ioc_succ_singleton, Finset.sum_filter, Finset.sum_singleton]
  split_ifs
  · apply Real.log_le_log (by positivity)
    exact_mod_cast (show (⌊x⌋₊ : ℝ)+1 ≤ x+1 from add_le_add_right (Nat.floor_le hx) 1)
  · exact Real.log_nonneg (by linarith only [hx])

/-- A continuous approximation to the signed normalized prime increment.
The numerator of the error costs at most the logarithms of two possible jumps. -/
theorem exists_continuous_normalizedPrimeIncrement_approx (β : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    ∃ V : ℝ → ℝ, Continuous V ∧ ∀ t, 0 ≤ t →
      |V t - normalizedPrimeIncrement β h t| ≤ (2*t+h+2)/Real.exp (β*t) := by
  let E := fun t => unitAverageTheta (Real.exp t) - Real.exp t
  have hE : Continuous E := (continuous_unitAverageTheta.comp Real.continuous_exp).sub Real.continuous_exp
  refine ⟨fun t => (E (t+h)-E t)/Real.exp (β*t),
    ((hE.comp (continuous_id.add continuous_const)).sub hE).div
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)) (fun _ => Real.exp_ne_zero _), ?_⟩
  have herr (s : ℝ) (hs : 0 ≤ s) : |E s-thetaLogError s| ≤ s+1 := by
    dsimp only [E, thetaLogError]
    rw [sub_sub_sub_cancel_right]
    refine (abs_unitAverageTheta_sub_theta (Real.exp_pos _).le).trans ?_
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he : 1 ≤ Real.exp s := Real.one_le_exp hs
    have htwo : 2 ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    rw [Real.exp_add]
    linarith only [he, mul_le_mul_of_nonneg_left htwo (Real.exp_pos s).le]
  intro t ht
  rw [normalizedPrimeIncrement, ← sub_div, abs_div, abs_of_pos (Real.exp_pos _)]
  apply div_le_div_of_nonneg_right _ (Real.exp_pos _).le
  rw [logStepIncrement, show E (t+h)-E t-(thetaLogError (t+h)-thetaLogError t) =
    (E (t+h)-thetaLogError (t+h))-(E t-thetaLogError t) by ring]
  exact (abs_sub _ _).trans ((add_le_add (herr _ (add_nonneg ht hh)) (herr _ ht)).trans_eq (by ring))

/-- From a point to a crest where the signs agree, suppose the squared wave
never falls below its initial value. Uniform squared-amplitude control on
that interval bounds the signed error even when the initial sign differs. -/
theorem sq_sub_le_on_wave_lobe {u D : ℝ → ℝ} {t s B : ℝ}
    (hu : ContinuousOn u (uIcc t s)) (hD : ContinuousOn D (uIcc t s))
    (hcrest : 0 < u s * D s)
    (hlobe : ∀ r ∈ uIcc t s, D t^2 ≤ D r^2)
    (hbound : ∀ r ∈ uIcc t s, |u r^2-D r^2| ≤ B) :
    (u t-D t)^2 ≤ 6*B := by
  have ht := hbound t left_mem_uIcc
  have hB := (abs_nonneg _).trans ht
  by_cases hsmall : D t^2 ≤ B
  · nlinarith only [(abs_le.mp ht).2, hsmall, sq_nonneg (u t+D t)]
  have hsign : 0 ≤ u t * D t := by
    by_contra! hn
    obtain ⟨r,hr,hr0⟩ := intermediate_value_uIcc (hu.mul hD)
      (show (0:ℝ) ∈ uIcc (u t*D t) (u s*D s) from mem_uIcc_of_le hn.le hcrest.le)
    have hl := hlobe r hr
    have hb := (abs_le.mp (hbound r hr)).1
    rcases mul_eq_zero.mp hr0 with he | he
    · rw [he, zero_pow two_ne_zero, zero_sub] at hb
      exact hsmall (by linarith only [hl,hb])
    · rw [he,zero_pow two_ne_zero] at hl
      exact hsmall (hl.trans hB)
  have hle : |u t-D t| ≤ |u t+D t| := sq_le_sq.mp (by nlinarith only [hsign])
  calc _ = |u t-D t| * |u t-D t| := by rw [← sq, sq_abs]
    _ ≤ |u t-D t| * |u t+D t| := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |u t^2-D t^2| := by rw [← abs_mul]; congr 1; ring
    _ ≤ 6*B := ht.trans (by linarith only [hB])

end GaloisForLFunctions.ExceptionalLayerTheory
