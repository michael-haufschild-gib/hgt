import GaloisForLFunctions.HTGeometry.NoncommutativeDiscreteDevelopment
import GaloisForLFunctions.RHTower.EulerDeletionNoncommutativeDevelopment

/-!
# Convergence of literal discrete Euler-deletion developments

For `Re s > 1/2`, the original ordered factors `1 + L(a_n * (n+1)^(-s))` converge
in every complete real normed algebra with unit norm one. Bounded coefficient prefixes,
finite variation, and square summability are all derived from the literal integer source.
No zero or higher-coherence assumption occurs. This is a convergence theorem, not an
identification of different deletion moduli or a critical-line selection theorem.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower
open GaloisForLFunctions.HTGeometry.NoncommutativeAbel

theorem arithmeticDirichletWeight_summable_sq {s : ℂ} (hs : 1/2 < s.re) :
    Summable (fun n => ‖arithmeticDirichletWeight s n‖ ^ 2) := by
  have hbase0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * s.re)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) 1).2 hbase0
  convert hbase using 1
  ext n
  rw [arithmeticDirichletWeight, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos (by positivity),
    pow_two, ← Real.exp_add]
  congr 1
  ring

def eulerDeletionDiscreteDevelopment {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (q : ℕ) (s : ℂ) (L : ℂ →L[ℝ] A) : ℕ → A :=
  orderedProduct (fun n => 1 + realDeletionCoefficient q n • L (arithmeticDirichletWeight s n))

theorem eulerDeletionDiscreteDevelopment_converges
    {A : Type*} [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (q : ℕ) {s : ℂ} (hs : 1/2 < s.re) (L : ℂ →L[ℝ] A) :
    ∃ P : A, Tendsto (eulerDeletionDiscreteDevelopment q s L) atTop (nhds P) := by
  have hs0 : 0 < s.re := by linarith
  apply ordered_discrete_converges (realDeletionCoefficient_partialSum_bound q)
  · simpa only [Function.comp_def, map_zero] using
      L.continuous.tendsto (0 : ℂ) |>.comp (arithmeticDirichletWeight_tendsto_zero hs0)
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((arithmeticDirichletWeight_summable_variation hs0).mul_left ‖L‖)
    rw [← map_sub]
    exact L.le_opNorm _
  · apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      ((arithmeticDirichletWeight_summable_sq hs).mul_left (‖L‖^(2 : ℕ)))
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (L.le_opNorm _)

end RHTower

