import GaloisForLFunctions.HTGeometry.NoncommutativeAbelDevelopment
import Mathlib.Analysis.Analytic.Basic

/-!
# Exact discrete noncommutative Abel development

The chronological factors are the literal `1 + a_n • b_n`, not exponentials. With bounded real
coefficient partial sums, a vanishing finite-variation algebra-valued weight, and summable squared
weight norms, their ordered products converge in a complete real normed algebra with unit norm one.

An exact finite conjugation retains the boundary factor. Its difference from the exponential
Abel seam is the explicit transported local Taylor error. No terms or order information are
removed, and the discrete and exponential limits are not asserted equal. Discrete factors may
be singular, so this theorem does not claim the limit is a unit.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.NoncommutativeAbel
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance noncommutativeDiscreteDevelopmentInst1 : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A

theorem summable_linear_exponential_error {z : ℕ → A}
    (hz : Tendsto z atTop (nhds 0)) (hs : Summable (fun n => ‖z n‖ ^ (2 : ℕ))) :
    Summable (fun n => ‖(1 + z n) - NormedSpace.exp (z n)‖) := by
  have hp := (NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos
    (NormedSpace.expSeries_radius_pos ℝ A)).isBigO_sub_partialSum_pow 2
  have hp' : (fun x : A => NormedSpace.exp x - (1 + x)) =O[nhds 0]
      (fun x => ‖x‖ ^ (2 : ℕ)) := by
    simpa [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      NormedSpace.expSeries_apply_eq] using hp
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hp'
  apply Summable.of_norm_bounded_eventually_nat (hs.mul_left C)
  filter_upwards [hz.eventually hC] with n hn
  simpa only [norm_pow, norm_norm, norm_sub_rev] using hn

omit [NormedAlgebra ℝ A] [CompleteSpace A] in
theorem summable_norm_sandwich {x y e : ℕ → A} {X Y : A}
    (hx : Tendsto x atTop (nhds X)) (hy : Tendsto y atTop (nhds Y))
    (he : Summable (fun n => ‖e n‖)) :
    Summable (fun n => ‖x n * e n * y n‖) := by
  obtain ⟨M, hM⟩ := hx.norm.bddAbove_range
  obtain ⟨K, hK⟩ := hy.norm.bddAbove_range
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((he.mul_left (max M 0)).mul_right (max K 0))
  exact (norm_mul_le _ _).trans (mul_le_mul
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      ((hM (Set.mem_range_self n)).trans (le_max_left _ _)) (norm_nonneg _)))
    ((hK (Set.mem_range_self n)).trans (le_max_left _ _)) (norm_nonneg _) (by positivity))

def discreteAbelSeam (a : ℕ → ℝ) (b : ℕ → A) (n : ℕ) : A :=
  (NormedSpace.exp (coefficientSum a n • b n) * (1 + a n • b n)) *
    NormedSpace.exp (-(coefficientSum a (n+1) • b (n+1)))

theorem orderedProduct_discrete_abel_factorization (a : ℕ → ℝ) (b : ℕ → A) (N : ℕ) :
    orderedProduct (fun n => 1 + a n • b n) N =
      orderedProduct (discreteAbelSeam a b) N *
        NormedSpace.exp (coefficientSum a N • b N) := by
  induction N with
  | zero => simp [orderedProduct, coefficientSum]
  | succ N ih =>
    rw [orderedProduct, ih, orderedProduct, discreteAbelSeam]
    simp only [mul_assoc, exp_neg_mul, mul_one]

theorem discreteAbelSeam_sub_abelSeam (a : ℕ → ℝ) (b : ℕ → A) (n : ℕ) :
    discreteAbelSeam a b n - abelSeam a b n =
      (NormedSpace.exp (coefficientSum a n • b n) *
        ((1 + a n • b n) - NormedSpace.exp (a n • b n))) *
      NormedSpace.exp (-(coefficientSum a (n+1) • b (n+1))) := by
  have he : NormedSpace.exp (coefficientSum a n • b n) *
      NormedSpace.exp (a n • b n) = NormedSpace.exp (coefficientSum a (n+1) • b n) := by
    rw [← NormedSpace.exp_add_of_commute
      (((Commute.refl (b n)).smul_left (coefficientSum a n)).smul_right (a n)),
      ← add_smul, ← coefficientSum_succ]
  simp only [mul_sub, sub_mul, he, discreteAbelSeam, abelSeam]

theorem coefficient_bound_of_partialSum_bound {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |coefficientSum a n| ≤ C) (n : ℕ) : |a n| ≤ 2 * C := by
  have he : a n = coefficientSum a (n+1) - coefficientSum a n := by
    rw [coefficientSum_succ]; ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith [ha (n+1), ha n])

theorem summable_discreteAbelSeam {a : ℕ → ℝ} {b : ℕ → A} {C : ℝ}
    (ha : ∀ n, |coefficientSum a n| ≤ C)
    (hb : Tendsto b atTop (nhds 0))
    (hd : Summable (fun n => ‖b n - b (n+1)‖))
    (hs : Summable (fun n => ‖b n‖ ^ (2 : ℕ))) :
    Summable (fun n => ‖discreteAbelSeam a b n - 1‖) := by
  have hz := tendsto_bounded_smul_zero (coefficient_bound_of_partialSum_bound ha) hb
  have hsq : Summable (fun n => ‖a n • b n‖ ^ (2 : ℕ)) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) (hs.mul_left ((2*C)^(2 : ℕ)))
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (sq_le_sq₀ (abs_nonneg _) (by linarith [abs_nonneg (a n),
      coefficient_bound_of_partialSum_bound ha n])).2 (coefficient_bound_of_partialSum_bound ha n)
  have hx := (NormedSpace.exp_continuous.tendsto (0 : A)).comp
    (tendsto_bounded_smul_zero ha hb)
  have hy := (NormedSpace.exp_continuous.tendsto (0 : A)).comp
    (show Tendsto (fun n => -(coefficientSum a (n+1) • b (n+1))) atTop (nhds 0) by
      simpa using ((tendsto_bounded_smul_zero ha hb).comp (tendsto_add_atTop_nat 1)).neg)
  have herr : Summable (fun n => ‖discreteAbelSeam a b n - abelSeam a b n‖) := by
    simpa only [Function.comp_def, discreteAbelSeam_sub_abelSeam] using
      summable_norm_sandwich hx hy (summable_linear_exponential_error hz hsq)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (herr.add (summable_abelSeam ha hb hd))
  calc
    ‖discreteAbelSeam a b n - 1‖ =
        ‖(discreteAbelSeam a b n - abelSeam a b n) + (abelSeam a b n - 1)‖ := by
      rw [sub_add_sub_cancel]
    _ ≤ _ := norm_add_le _ _

theorem ordered_discrete_converges [NormOneClass A]
    {a : ℕ → ℝ} {b : ℕ → A} {C : ℝ}
    (ha : ∀ n, |coefficientSum a n| ≤ C)
    (hb : Tendsto b atTop (nhds 0))
    (hd : Summable (fun n => ‖b n - b (n+1)‖))
    (hs : Summable (fun n => ‖b n‖ ^ (2 : ℕ))) :
    ∃ P : A, Tendsto (orderedProduct (fun n => 1 + a n • b n)) atTop (nhds P) := by
  obtain ⟨P, hP⟩ := orderedProduct_converges (summable_discreteAbelSeam ha hb hd hs)
  have hlast := (NormedSpace.exp_continuous.tendsto (0 : A)).comp
    (tendsto_bounded_smul_zero ha hb)
  refine ⟨P, ?_⟩
  simpa only [Function.comp_def, NormedSpace.exp_zero, mul_one,
    ← orderedProduct_discrete_abel_factorization] using hP.mul hlast

end GaloisForLFunctions.HTGeometry.NoncommutativeAbel

