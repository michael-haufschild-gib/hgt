/-
# Closed primitive Dirichlet L zero-density subfamilies

This module makes the primitive-character family in a source-style
Dirichlet-L zero-density sum literal.  It proves that the primitive
subfamily's vertical zero-box count is dominated by the already formalized
all-nonprincipal count, both at a fixed modulus and through a finite conductor
cutoff.  The result does not create the missing conductor-uniform exponent.

No RH, GRH, exceptional-zero, or zero-density premise is used.
-/
import GaloisForLFunctions.RHTower.DirichletLZeroDensityRange

open Complex Metric

noncomputable section

namespace RHTower

/-- Literal vertical zero-box count over the primitive nonprincipal characters at a concrete
modulus.  It is a filtered finite sum over the already certified nonprincipal character family. -/
noncomputable def completedLFunctionPrimitiveFamilyZeroDensityBoxCount
    (n : ℕ) (σ H : ℝ) : ℝ := by
  classical
  exact ∑ χ : NonprincipalDirichletCharacter n,
    if DirichletCharacter.IsPrimitive χ.1 then
      completedLFunctionZeroDensityBoxCount n χ σ H else 0

/-- A one-character literal vertical zero-box count is nonnegative. -/
theorem completedLFunction_zeroDensityBoxCount_nonneg
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ H : ℝ) :
    0 ≤ completedLFunctionZeroDensityBoxCount n χ σ H := by
  change (0 : ℝ) ≤ ↑(∑ᶠ u, MeromorphicOn.divisor
    (DirichletCharacter.completedLFunction χ.1)
    (completedLFunctionZeroDensityBox σ H) u)
  exact_mod_cast finsum_nonneg fun u =>
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      ((completedLFunction_analyticOnNhd n χ).mono (Set.subset_univ _)) u

/-- The primitive nonprincipal character zero-box count is bounded by the full nonprincipal
family count at the same concrete modulus. -/
theorem completedLFunction_primitiveFamily_zeroDensityBoxCount_le
    (n : ℕ) (σ H : ℝ) :
    completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H ≤
      completedLFunctionFamilyZeroDensityBoxCount n σ H := by
  classical
  rw [completedLFunctionPrimitiveFamilyZeroDensityBoxCount,
    completedLFunctionFamilyZeroDensityBoxCount]
  apply Finset.sum_le_sum
  intro χ hχ
  by_cases hprim : DirichletCharacter.IsPrimitive χ.1
  · simp [hprim]
  · simp [hprim, completedLFunction_zeroDensityBoxCount_nonneg]

/-- Closed fixed-modulus bound for the literal primitive nonprincipal character zero-box family.
It inherits the all-nonprincipal constant; it is not a uniform density theorem. -/
theorem completedLFunction_primitiveFamily_zeroDensityBoxCount_growth
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ σ H : ℝ,
      completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H ≤
        C * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
  obtain ⟨C, hCpos, hCbound⟩ := completedLFunction_family_zeroDensityBoxCount_growth n
  exact ⟨C, hCpos, fun σ H ↦
    (completedLFunction_primitiveFamily_zeroDensityBoxCount_le n σ H).trans (hCbound σ H)⟩

/-- Literal vertical zero-box count over every primitive nonprincipal character at every modulus
from `1` through a fixed conductor cutoff. -/
noncomputable def completedLFunctionPrimitiveRangeZeroDensityBoxCount
    (Q : ℕ) (σ H : ℝ) : ℝ :=
  ∑ n ∈ Finset.range Q, completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H

/-- The primitive nonprincipal family through a fixed conductor cutoff is dominated by the full
nonprincipal conductor-range count. -/
theorem completedLFunction_primitiveRange_zeroDensityBoxCount_le
    (Q : ℕ) (σ H : ℝ) :
    completedLFunctionPrimitiveRangeZeroDensityBoxCount Q σ H ≤
      completedLFunctionRangeZeroDensityBoxCount Q σ H := by
  rw [completedLFunctionPrimitiveRangeZeroDensityBoxCount,
    completedLFunctionRangeZeroDensityBoxCount]
  exact Finset.sum_le_sum (fun n hn ↦
    completedLFunction_primitiveFamily_zeroDensityBoxCount_le n σ H)

/-- Closed finite-conductor vertical zero-box bound for the literal primitive nonprincipal
character family.  Its constant remains cutoff-dependent. -/
theorem completedLFunction_primitiveRange_zeroDensityBoxCount_growth
    (Q : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ σ H : ℝ,
      completedLFunctionPrimitiveRangeZeroDensityBoxCount Q σ H ≤
        C * (5 + |σ| + |H|) * Real.log (6 + |σ| + |H|) := by
  obtain ⟨C, hCpos, hCbound⟩ := completedLFunction_range_zeroDensityBoxCount_growth Q
  exact ⟨C, hCpos, fun σ H ↦
    (completedLFunction_primitiveRange_zeroDensityBoxCount_le Q σ H).trans (hCbound σ H)⟩

end RHTower
