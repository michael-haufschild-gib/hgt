/-
# Analytic natural-scale spacing for Dirichlet-L zero windows

Chen--Gupta--Li's zero-detection selection needs a locally bounded,
well-spaced packet.  The base selector used the exact zero-copy cardinality
as capacity.  This file instead turns the closed Jensen vertical-window
envelope into a natural number capacity and supplies the same selection at
every natural spacing scale.  Its constant remains character-dependent, so
this is analytic infrastructure rather than the source's uniform local
`O(log qT)` estimate.

No RH, GRH, zero-density premise, or caller-supplied capacity bound is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowRows

open Finset

noncomputable section

namespace RHTower

/-- The Jensen envelope for one centered vertical zero window.  Its positive
constant is selected internally from the already proved analytic zero-count
theorem for this certified character. -/
noncomputable def cglZeroDensityVerticalWindowAnalyticEnvelope
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℝ :=
  (Classical.choose (completedLFunction_zeroDensityBoxCount_growth n χ)) *
    (5 + |σ| + |τ| + H) * Real.log (6 + |σ| + |τ| + H)

/-- The literal centered-window multiplicity count is bounded by its closed
Jensen envelope. -/
theorem completedLFunction_zeroDensityVerticalWindowCount_le_analyticEnvelope
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
      cglZeroDensityVerticalWindowAnalyticEnvelope n χ σ τ H := by
  have hbox := completedLFunction_zeroDensityVerticalWindowCount_le_box n χ σ τ H
  have hgrowth := (Classical.choose_spec
    (completedLFunction_zeroDensityBoxCount_growth n χ)).2
  have hτH : 0 ≤ |τ| + (H : ℝ) := by positivity
  have habs : |(|τ| + (H : ℝ))| = |τ| + H := abs_of_nonneg hτH
  calc
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
        completedLFunctionZeroDensityBoxCount n χ σ (|τ| + H) := hbox
    _ ≤ (Classical.choose (completedLFunction_zeroDensityBoxCount_growth n χ)) *
        (5 + |σ| + |(|τ| + (H : ℝ))|) *
          Real.log (6 + |σ| + |(|τ| + (H : ℝ))|) :=
      hgrowth σ (|τ| + H)
    _ = cglZeroDensityVerticalWindowAnalyticEnvelope n χ σ τ H := by
      unfold cglZeroDensityVerticalWindowAnalyticEnvelope
      rw [habs]
      congr 2 <;> ring

/-- Closed local-capacity data at arbitrary natural spacing.  The capacity is
the natural ceiling of the Jensen envelope, not the unknown zero-copy count. -/
noncomputable def cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ) :
    CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H where
  spacing := (K + 1 : ℕ)
  spacing_pos := by positivity
  capacity := Nat.ceil (cglZeroDensityVerticalWindowAnalyticEnvelope n χ σ τ H)
  bucket_card_le := by
    intro b
    let S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :=
      (Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).filter
        (fun r => bucket (K + 1 : ℕ)
          (cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r) = b)
    have hS_card : S.card ≤ cglZeroDensityVerticalWindowCopyCard n χ σ τ H := by
      dsimp [S]
      calc
        ((Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).filter
          (fun r => bucket (K + 1 : ℕ)
            (cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r) = b)).card ≤
            (Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = cglZeroDensityVerticalWindowCopyCard n χ σ τ H := by simp
    have hS_real : (S.card : ℝ) ≤
        completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H := by
      rw [← card_cglZeroDensityVerticalWindowZeroCopy_eq_count]
      exact_mod_cast hS_card
    have hceil : cglZeroDensityVerticalWindowAnalyticEnvelope n χ σ τ H ≤
        (Nat.ceil (cglZeroDensityVerticalWindowAnalyticEnvelope n χ σ τ H) : ℝ) :=
      Nat.le_ceil _
    have hcast : (S.card : ℝ) ≤
        (Nat.ceil (cglZeroDensityVerticalWindowAnalyticEnvelope n χ σ τ H) : ℝ) :=
      hS_real.trans
        ((completedLFunction_zeroDensityVerticalWindowCount_le_analyticEnvelope n χ σ τ H).trans hceil)
    exact_mod_cast hcast

/-- Canonical `(K+1)`-separated selection whose capacity is supplied by the
closed analytic envelope. -/
noncomputable def cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ) :
    Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :=
  Classical.choose (exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
    (cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity n χ σ τ H K))

/-- The analytic natural-scale selection controls the exact
multiplicity-weighted zero count without a caller-supplied local bound. -/
theorem cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection_count
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ) :
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
      (2 * (cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity n χ σ τ H K).capacity *
        (cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection n χ σ τ H K).card : ℕ) := by
  exact (Classical.choose_spec
    (exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
      (cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity n χ σ τ H K))).1

/-- Distinct rows in the analytic natural-scale selection are separated by
the literal natural scale `K+1`. -/
theorem cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection_separated
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ)
    (r s : Fin (Fintype.card
      (↑(cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection n χ σ τ H K))))
    (hrs : r ≠ s) :
    (K + 1 : ℕ) ≤
      |(cglZeroDensityVerticalWindowSelectedRows n χ σ τ H
        (cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection n χ σ τ H K) r).time -
        (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H
          (cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection n χ σ τ H K) s).time| := by
  unfold cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection
  simpa only [cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity] using
    (Classical.choose_spec
      (exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
        (cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity n χ σ τ H K))).2 r s hrs

end RHTower
