/-
# Closed enlargement transport for Dirichlet L zero-density boxes

The zero-detection method passes from a source rectangle to slightly enlarged
boxes when it selects well-spaced zero representatives.  This module proves
that exact transport law for the corpus's literal multiplicity-weighted
completed-Dirichlet-L zero counts.  It applies to one nonprincipal character,
the full character family, the primitive subfamily, and every finite conductor
range.

No RH, GRH, exceptional-zero, zero-density, or counting premise is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityPrimitive

open Complex Metric

noncomputable section

namespace RHTower

/-- Leftward expansion of a zero-density abscissa by a nonnegative radius. -/
def cglZeroDensityExpandedAbscissa (σ : ℝ) (δ : NNReal) : ℝ := σ - δ

/-- Upward expansion of a zero-density height by a nonnegative radius. -/
def cglZeroDensityExpandedHeight (H : ℝ) (δ : NNReal) : ℝ := H + δ

/-- A literal completed-Dirichlet-L zero box is contained in its closed
leftward/upward expansion. -/
theorem completedLFunction_zeroDensityBoxCount_le_expand
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ H : ℝ) (δ : NNReal) :
    completedLFunctionZeroDensityBoxCount n χ σ H ≤
      completedLFunctionZeroDensityBoxCount n χ
        (cglZeroDensityExpandedAbscissa σ δ)
        (cglZeroDensityExpandedHeight H δ) := by
  let f := DirichletCharacter.completedLFunction χ.1
  let U := completedLFunctionZeroDensityBox
    (cglZeroDensityExpandedAbscissa σ δ) (cglZeroDensityExpandedHeight H δ)
  let V := completedLFunctionZeroDensityBox σ H
  let D := closedBall (2 : ℂ) (4 + |cglZeroDensityExpandedAbscissa σ δ| +
    |cglZeroDensityExpandedHeight H δ|)
  have hVU : V ⊆ U := by
    intro z hz
    change σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ H at hz
    change cglZeroDensityExpandedAbscissa σ δ ≤ z.re ∧ z.re ≤ 1 ∧
      |z.im| ≤ cglZeroDensityExpandedHeight H δ
    constructor
    · unfold cglZeroDensityExpandedAbscissa
      linarith [δ.2]
    constructor
    · exact hz.2.1
    · unfold cglZeroDensityExpandedHeight
      linarith [δ.2]
  have hUD : U ⊆ D := by
    exact completedLFunction_zeroDensityBox_subset_disc
      (cglZeroDensityExpandedAbscissa σ δ) (cglZeroDensityExpandedHeight H δ)
  have hVD : V ⊆ D := fun z hz => hUD (hVU hz)
  have hf : AnalyticOnNhd ℂ f Set.univ := completedLFunction_analyticOnNhd n χ
  have hfU : AnalyticOnNhd ℂ f U := hf.mono (Set.subset_univ U)
  have hfV : AnalyticOnNhd ℂ f V := hf.mono (Set.subset_univ V)
  have hfD : AnalyticOnNhd ℂ f D := hf.mono (Set.subset_univ D)
  change (↑(∑ᶠ u, MeromorphicOn.divisor f V u) : ℝ) ≤
    (↑(∑ᶠ u, MeromorphicOn.divisor f U u) : ℝ)
  exact_mod_cast finsum_le_finsum'
    (hfD.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall ..) hVD)
    (hfD.meromorphicOn.divisor_support_finite_of_subset (isCompact_closedBall ..) hUD)
    (fun u => by
      change (MeromorphicOn.divisor f V) u ≤ (MeromorphicOn.divisor f U) u
      by_cases hu : u ∈ V
      · rw [MeromorphicOn.divisor_apply hfV.meromorphicOn hu,
          MeromorphicOn.divisor_apply hfU.meromorphicOn (hVU hu)]
      · simp only [MeromorphicOn.divisor_def, hu, and_false, ite_false]
        exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfU u)

/-- Closed enlargement transport for a complete finite nonprincipal
Dirichlet-character family at a fixed modulus. -/
theorem completedLFunction_family_zeroDensityBoxCount_le_expand
    (n : ℕ) (σ H : ℝ) (δ : NNReal) :
    completedLFunctionFamilyZeroDensityBoxCount n σ H ≤
      completedLFunctionFamilyZeroDensityBoxCount n
        (cglZeroDensityExpandedAbscissa σ δ)
        (cglZeroDensityExpandedHeight H δ) := by
  unfold completedLFunctionFamilyZeroDensityBoxCount
  exact Finset.sum_le_sum (fun χ _ =>
    completedLFunction_zeroDensityBoxCount_le_expand n χ σ H δ)

/-- Closed enlargement transport for the primitive nonprincipal family at a
fixed modulus. -/
theorem completedLFunction_primitiveFamily_zeroDensityBoxCount_le_expand
    (n : ℕ) (σ H : ℝ) (δ : NNReal) :
    completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ H ≤
      completedLFunctionPrimitiveFamilyZeroDensityBoxCount n
        (cglZeroDensityExpandedAbscissa σ δ)
        (cglZeroDensityExpandedHeight H δ) := by
  classical
  unfold completedLFunctionPrimitiveFamilyZeroDensityBoxCount
  apply Finset.sum_le_sum
  intro χ hχ
  by_cases hprim : DirichletCharacter.IsPrimitive χ.1
  · simp only [hprim, if_pos]
    exact completedLFunction_zeroDensityBoxCount_le_expand n χ σ H δ
  · simp [hprim]

/-- Closed enlargement transport for the primitive nonprincipal family across
every modulus in a finite conductor range. -/
theorem completedLFunction_primitiveRange_zeroDensityBoxCount_le_expand
    (Q : ℕ) (σ H : ℝ) (δ : NNReal) :
    completedLFunctionPrimitiveRangeZeroDensityBoxCount Q σ H ≤
      completedLFunctionPrimitiveRangeZeroDensityBoxCount Q
        (cglZeroDensityExpandedAbscissa σ δ)
        (cglZeroDensityExpandedHeight H δ) := by
  unfold completedLFunctionPrimitiveRangeZeroDensityBoxCount
  exact Finset.sum_le_sum (fun n _ =>
    completedLFunction_primitiveFamily_zeroDensityBoxCount_le_expand n σ H δ)

end RHTower
