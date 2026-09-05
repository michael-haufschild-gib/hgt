import GaloisForLFunctions.RHTower.EulerDeletionNoncommutativeDevelopment
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondShadow

/-!
# Abelian shadow of Euler-deletion development

The noncommutative Euler-deletion development exists throughout `Re s > 0`.  This file identifies
its commutative shadow exactly.  In any commutative complete normed real algebra, the ordered
exponential product is the exponential of the mapped scalar deletion prefix.  Consequently every
positive-half-plane zeta zero sends that shadow to the unit.

Thus any deletion-development information not already contained in scalar zero landing must live
in genuinely noncommutative commutator grades.  No claim that such a grade yields refinement
coherence is made here.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry.NoncommutativeAbel

/-- One algebra-valued exponent in the deletion development. -/
def eulerDeletionMappedJump
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (q : ℕ) (s : ℂ) (L : ℂ →L[ℝ] A) (n : ℕ) : A :=
  realDeletionCoefficient q n • L (arithmeticDirichletWeight s n)

/-- The mapped exponent is exactly the real-linear image of the complex weighted jump. -/
theorem eulerDeletionMappedJump_eq
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (q : ℕ) (s : ℂ) (L : ℂ →L[ℝ] A) (n : ℕ) :
    eulerDeletionMappedJump q s L n = L (eulerDeletionWeightedJump q s n) := by
  rw [eulerDeletionMappedJump, eulerDeletionWeightedJump,
    eulerDeletionDirichletCoefficient, realDeletionCoefficient,
    arithmeticDirichletWeight, ← L.map_smul]
  congr 1

/-- In a commutative target, chronological exponentials collapse to one exponential of their sum. -/
theorem eulerDeletionDevelopment_eq_exp_sum_mapped
    {A : Type*} [NormedCommRing A] [NormOneClass A] [NormedAlgebra ℝ A]
    [CompleteSpace A]
    (q : ℕ) (s : ℂ) (L : ℂ →L[ℝ] A) (N : ℕ) :
    eulerDeletionDevelopment q s L N =
      NormedSpace.exp (∑ n ∈ Finset.range N, eulerDeletionMappedJump q s L n) := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  unfold eulerDeletionDevelopment
  induction N with
  | zero => simp [orderedProduct]
  | succ N ih =>
      rw [orderedProduct, Finset.sum_range_succ, ih]
      exact (NormedSpace.exp_add_of_commute (Commute.all _ _)).symm

/-- The finite commutative shadow is the exponential of the mapped scalar deletion endpoint. -/
theorem eulerDeletionDevelopment_eq_exp_map_prefix
    {A : Type*} [NormedCommRing A] [NormOneClass A] [NormedAlgebra ℝ A]
    [CompleteSpace A]
    (q : ℕ) (s : ℂ) (L : ℂ →L[ℝ] A) (N : ℕ) :
    eulerDeletionDevelopment q s L N =
      NormedSpace.exp (L (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q s n)) := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  rw [eulerDeletionDevelopment_eq_exp_sum_mapped]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact eulerDeletionMappedJump_eq q s L n

/-- At every positive-half-plane zeta zero, every commutative development limit is the unit. -/
theorem eulerDeletionDevelopmentLimit_eq_one_of_zeta_zero
    {A : Type*} [NormedCommRing A] [NormOneClass A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (q : ℕ) {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0)
    (L : ℂ →L[ℝ] A) :
    eulerDeletionDevelopmentLimit q ⟨rho, hrhoRe⟩ L = 1 := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℝ A
  have hprefix := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    q hrhoRe hrho1 hzeta
  have hmapped : Tendsto
      (fun N => L (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, map_zero] using
      L.continuous.tendsto 0 |>.comp hprefix
  have hexp : Tendsto
      (fun N => NormedSpace.exp
        (L (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n)))
      atTop (nhds 1) := by
    simpa only [Function.comp_def, NormedSpace.exp_zero] using
      (NormedSpace.exp_continuous.tendsto (0 : A)).comp hmapped
  have hdevelopment : Tendsto (eulerDeletionDevelopment q rho L) atTop (nhds 1) := by
    apply hexp.congr'
    exact Filter.Eventually.of_forall fun N =>
      (eulerDeletionDevelopment_eq_exp_map_prefix q rho L N).symm
  exact tendsto_nhds_unique
    (tendsto_eulerDeletionDevelopment q ⟨rho, hrhoRe⟩ L) hdevelopment

end RHTower
