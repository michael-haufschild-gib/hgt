import GaloisForLFunctions.PeriodRigidity
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Rank-three period rigidity

Three `ℚ`-linearly independent complex periods generate a rank-three integer subgroup of the
two-dimensional real vector space `ℂ`. Such a subgroup need not be dense, but it cannot be
discrete. This file turns nondiscreteness into a sequence of nonzero periods converging to zero
and combines that fact with meromorphic normal-form rigidity.
-/

namespace GaloisForLFunctions

open Filter
open scoped Topology

/-- The integer span of three `ℚ`-linearly independent complex numbers is not discrete. -/
theorem not_discrete_intSpan_fin_three (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ¬ DiscreteTopology (Submodule.span ℤ (Set.range v)) := by
  intro hd
  have hvz : LinearIndependent ℤ v := hv.restrict_scalars' ℤ
  have hz : Set.finrank ℤ (Set.range v) = 3 := by
    change Module.finrank ℤ (Submodule.span ℤ (Set.range v)) = 3
    rw [finrank_span_eq_card hvz]
    simp
  have heq := Real.finrank_eq_int_finrank_of_discrete (s := Set.range v) hd
  have hrle : Set.finrank ℝ (Set.range v) ≤ 2 := by
    calc
      Set.finrank ℝ (Set.range v) ≤ Module.finrank ℝ ℂ := Submodule.finrank_le _
      _ = 2 := Complex.finrank_real_complex
  omega

/-- Every nondiscrete integer submodule of `ℂ` contains nonzero elements converging to zero. -/
theorem exists_small_nonzero_of_not_discrete_intSubmodule
    (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L) :
    ∃ p : ℕ → ℂ, (∀ n, p n ∈ L) ∧ (∀ n, p n ≠ 0) ∧ Tendsto p atTop (𝓝 0) := by
  classical
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hrpos : ∀ n, 0 < r n := fun n => by positivity
  have hex : ∀ n, ∃ q : L, q ∈ Metric.ball 0 (r n) ∧ q ≠ 0 := by
    intro n
    by_contra h
    push Not at h
    apply hL
    apply discreteTopology_iff_isOpen_singleton_zero.mpr
    have hsub : Metric.ball (0 : L) (r n) ⊆ {0} := by
      intro q hq
      simpa using h q hq
    have hzero : (0 : L) ∈ Metric.ball 0 (r n) := by simp [hrpos n]
    have heq : Metric.ball (0 : L) (r n) = {0} := by
      apply Set.Subset.antisymm hsub
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      subst q
      exact hzero
    rw [← heq]
    exact Metric.isOpen_ball
  choose q hqball hqne using hex
  refine ⟨fun n => (q n : ℂ), fun n => (q n).2, ?_, ?_⟩
  · intro n hn
    apply hqne n
    apply Subtype.ext
    exact hn
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero
    · exact fun n => dist_nonneg
    · intro n
      exact le_of_lt (hqball n)
    · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- A rank-three period lattice supplies arbitrarily small nonzero periods. -/
theorem exists_small_rankThree_periods (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v) :
    ∃ p : ℕ → ℂ, (∀ n, p n ∈ Submodule.span ℤ (Set.range v)) ∧
      (∀ n, p n ≠ 0) ∧ Tendsto p atTop (𝓝 0) :=
  exists_small_nonzero_of_not_discrete_intSubmodule _ (not_discrete_intSpan_fin_three v hv)

/-- A meromorphic normal-form function invariant under the integer span of three
`ℚ`-linearly independent periods is constant. This is the analytic joint-constant collapse used
by the paired difference-differential Galois argument. -/
theorem meromorphicNF_constant_of_rankThree_periods
    (f : ℂ → ℂ) (hf : MeromorphicNFOn f Set.univ)
    (v : Fin 3 → ℂ) (hv : LinearIndependent ℚ v)
    (hperiod : ∀ p ∈ Submodule.span ℤ (Set.range v), Function.Periodic f p) :
    ∀ x y, f x = f y := by
  obtain ⟨p, hp_mem, hp_ne, hp_zero⟩ := exists_small_rankThree_periods v hv
  exact meromorphicNF_constant_of_small_periods f hf p hp_zero hp_ne
    (fun n => hperiod (p n) (hp_mem n))

end GaloisForLFunctions
