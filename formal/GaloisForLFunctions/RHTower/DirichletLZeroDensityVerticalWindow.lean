/-
# Centered Dirichlet-L zero-density windows

The zero-detection spacing step uses local windows centered at an ordinate,
whereas the corpus's base zero-density carrier is symmetric around zero.  This
module makes the centered multiplicity-weighted window count literal and
proves it is controlled by the corresponding symmetric box.  The comparison
is carried through all nonprincipal, primitive, finite-range, and
primitive-conductor-divisor aggregations used by Chen--Gupta--Li Section 12
and Bondarenko--Heap Lemma 10.

No RH, GRH, local zero-density bound, or zero-detection premise is used.
-/

import GaloisForLFunctions.RHTower.BondarenkoHeapLemmaTenConductorAggregation

open Complex Metric

noncomputable section

namespace RHTower

/-- A source-style vertical zero window centered at ordinate `τ` and with a
certified nonnegative half-width. -/
def cglZeroDensityVerticalWindow (σ τ : ℝ) (H : NNReal) : Set ℂ :=
  {z | σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im - τ| ≤ H}

/-- A centered vertical window lies in the symmetric zero-density box whose
height is its center magnitude plus its half-width. -/
theorem cglZeroDensityVerticalWindow_subset_zeroDensityBox (σ τ : ℝ) (H : NNReal) :
    cglZeroDensityVerticalWindow σ τ H ⊆
      completedLFunctionZeroDensityBox σ (|τ| + H) := by
  intro z hz
  change σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im - τ| ≤ H at hz
  change σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ |τ| + H
  refine ⟨hz.1, hz.2.1, ?_⟩
  calc
    |z.im| = |(z.im - τ) + τ| := by ring_nf
    _ ≤ |z.im - τ| + |τ| := abs_add_le _ _
    _ ≤ |τ| + H := by linarith

/-- Multiplicity-weighted count of zeros of one completed nonprincipal
Dirichlet L-function in a centered vertical window. -/
def completedLFunctionZeroDensityVerticalWindowCount
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℝ :=
  (↑(∑ᶠ u, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.1)
    (cglZeroDensityVerticalWindow σ τ H) u) : ℝ)

/-- A one-character centered-window count is controlled by the symmetric
zero-density box containing it. -/
theorem completedLFunction_zeroDensityVerticalWindowCount_le_box
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
      completedLFunctionZeroDensityBoxCount n χ σ (|τ| + H) := by
  let f := DirichletCharacter.completedLFunction χ.1
  let U := completedLFunctionZeroDensityBox σ (|τ| + H)
  let V := cglZeroDensityVerticalWindow σ τ H
  let D := closedBall (2 : ℂ) (4 + |σ| + |(|τ| + (H : ℝ))|)
  have hVU : V ⊆ U := cglZeroDensityVerticalWindow_subset_zeroDensityBox σ τ H
  have hUD : U ⊆ D := by
    exact completedLFunction_zeroDensityBox_subset_disc σ (|τ| + H)
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

/-- Total centered-window count over the finite nonprincipal character family
at one modulus. -/
def completedLFunctionFamilyZeroDensityVerticalWindowCount
    (n : ℕ) (σ τ : ℝ) (H : NNReal) : ℝ :=
  ∑ χ : NonprincipalDirichletCharacter n,
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H

/-- Family centered-window count is controlled by the corresponding symmetric
family zero-density box. -/
theorem completedLFunction_family_zeroDensityVerticalWindowCount_le_box
    (n : ℕ) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionFamilyZeroDensityVerticalWindowCount n σ τ H ≤
      completedLFunctionFamilyZeroDensityBoxCount n σ (|τ| + H) := by
  unfold completedLFunctionFamilyZeroDensityVerticalWindowCount
    completedLFunctionFamilyZeroDensityBoxCount
  exact Finset.sum_le_sum (fun χ hχ =>
    completedLFunction_zeroDensityVerticalWindowCount_le_box n χ σ τ H)

/-- Centered-window count restricted to primitive nonprincipal characters. -/
noncomputable def completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
    (n : ℕ) (σ τ : ℝ) (H : NNReal) : ℝ := by
  classical
  exact ∑ χ : NonprincipalDirichletCharacter n,
    if DirichletCharacter.IsPrimitive χ.1 then
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H else 0

/-- Primitive centered-window count is controlled by the corresponding
primitive symmetric zero-density box. -/
theorem completedLFunction_primitiveFamily_zeroDensityVerticalWindowCount_le_box
    (n : ℕ) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount n σ τ H ≤
      completedLFunctionPrimitiveFamilyZeroDensityBoxCount n σ (|τ| + H) := by
  classical
  unfold completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount
    completedLFunctionPrimitiveFamilyZeroDensityBoxCount
  apply Finset.sum_le_sum
  intro χ hχ
  by_cases hprim : DirichletCharacter.IsPrimitive χ.1
  · simp only [hprim, if_pos]
    exact completedLFunction_zeroDensityVerticalWindowCount_le_box n χ σ τ H
  · simp [hprim]

/-- Centered-window count over primitive nonprincipal characters through a
finite modulus cutoff. -/
noncomputable def completedLFunctionPrimitiveRangeZeroDensityVerticalWindowCount
    (Q : ℕ) (σ τ : ℝ) (H : NNReal) : ℝ :=
  ∑ n ∈ Finset.range Q,
    completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount n σ τ H

/-- Finite primitive-conductor range comparison from centered windows to
symmetric density boxes. -/
theorem completedLFunction_primitiveRange_zeroDensityVerticalWindowCount_le_box
    (Q : ℕ) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionPrimitiveRangeZeroDensityVerticalWindowCount Q σ τ H ≤
      completedLFunctionPrimitiveRangeZeroDensityBoxCount Q σ (|τ| + H) := by
  unfold completedLFunctionPrimitiveRangeZeroDensityVerticalWindowCount
    completedLFunctionPrimitiveRangeZeroDensityBoxCount
  exact Finset.sum_le_sum (fun n hn =>
    completedLFunction_primitiveFamily_zeroDensityVerticalWindowCount_le_box n σ τ H)

/-- Centered-window primitive-conductor aggregation, matching the divisor sum
in Bondarenko--Heap Lemma 10. -/
noncomputable def completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
    (q : ℕ) (σ τ : ℝ) (H : NNReal) : ℝ :=
  ∑ d ∈ q.divisors,
    completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount (d - 1) σ τ H

/-- The primitive-conductor centered-window aggregation is controlled by the
source's corresponding symmetric divisor box. -/
theorem completedLFunction_primitiveDivisor_zeroDensityVerticalWindowCount_le_box
    (q : ℕ) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount q σ τ H ≤
      completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ (|τ| + H) := by
  unfold completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount
    completedLFunctionPrimitiveDivisorZeroDensityBoxCount
  exact Finset.sum_le_sum (fun d hd =>
    completedLFunction_primitiveFamily_zeroDensityVerticalWindowCount_le_box (d - 1) σ τ H)

/-- Every fixed primitive-conductor family has a closed centered-window
envelope.  It is a local counting foundation, not a conductor-uniform density
exponent. -/
theorem completedLFunction_primitiveDivisor_zeroDensityVerticalWindowCount_growth
    (q : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ σ τ : ℝ, ∀ H : NNReal,
      completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount q σ τ H ≤
        C * (5 + |σ| + |τ| + H) * Real.log (6 + |σ| + |τ| + H) := by
  obtain ⟨C, hC, hbound⟩ := completedLFunction_primitiveDivisor_zeroDensityBoxCount_growth q
  refine ⟨C, hC, fun σ τ H => ?_⟩
  calc
    completedLFunctionPrimitiveDivisorZeroDensityVerticalWindowCount q σ τ H ≤
        completedLFunctionPrimitiveDivisorZeroDensityBoxCount q σ (|τ| + H) :=
      completedLFunction_primitiveDivisor_zeroDensityVerticalWindowCount_le_box q σ τ H
    _ ≤ C * (5 + |σ| + |(|τ| + (H : ℝ))|) *
        Real.log (6 + |σ| + |(|τ| + (H : ℝ))|) :=
      hbound σ (|τ| + H)
    _ = C * (5 + |σ| + |τ| + H) * Real.log (6 + |σ| + |τ| + H) := by
      have hτH : 0 ≤ |τ| + (H : ℝ) := by positivity
      have habs : |(|τ| + (H : ℝ))| = |τ| + H := abs_of_nonneg hτH
      rw [habs]
      congr 2 <;> ring

end RHTower
