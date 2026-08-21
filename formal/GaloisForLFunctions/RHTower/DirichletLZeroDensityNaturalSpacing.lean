/-
# Closed natural-scale zero-density spacing packets

For every natural scale `K`, this module extracts a `(K+1)`-separated finite
packet from the literal multiplicity-aware zero copies.  The unconditional
capacity is the full finite packet, so the resulting count loss is explicit.
This gives the zero-density side of the coarse spacing required before a
source-scale large-value theorem is applied.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowRows

noncomputable section

namespace RHTower

/-- Closed local-capacity certificate at natural spacing `K+1`. -/
noncomputable def cglZeroDensityVerticalWindowNaturalLocalCapacity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ) :
    CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H where
  spacing := (K + 1 : ℕ)
  spacing_pos := by positivity
  capacity := cglZeroDensityVerticalWindowCopyCard n χ σ τ H
  bucket_card_le := by
    intro b
    calc
      ((Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).filter
        (fun r => bucket (K + 1 : ℕ)
          (cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r) = b)).card ≤
          (Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = cglZeroDensityVerticalWindowCopyCard n χ σ τ H := by simp

/-- Canonical `(K+1)`-separated selection from the finite zero-copy packet. -/
noncomputable def cglZeroDensityVerticalWindowNaturalWellSpacedSelection
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ) :
    Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :=
  Classical.choose (exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
    (cglZeroDensityVerticalWindowNaturalLocalCapacity n χ σ τ H K))

/-- Closed zero-count control for the natural-scale separated selection. -/
theorem cglZeroDensityVerticalWindowNaturalWellSpacedSelection_count
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ) :
    completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
      (2 * cglZeroDensityVerticalWindowCopyCard n χ σ τ H *
        (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ σ τ H K).card : ℕ) := by
  exact (Classical.choose_spec
    (exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
      (cglZeroDensityVerticalWindowNaturalLocalCapacity n χ σ τ H K))).1

/-- The canonical selected rows carry their certified natural-scale spacing. -/
theorem cglZeroDensityVerticalWindowNaturalWellSpacedSelection_separated
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) (K : ℕ)
    (r s : Fin (Fintype.card
      (↑(cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ σ τ H K))))
    (hrs : r ≠ s) :
    (K + 1 : ℕ) ≤
      |(cglZeroDensityVerticalWindowSelectedRows n χ σ τ H
        (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ σ τ H K) r).time -
        (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H
          (cglZeroDensityVerticalWindowNaturalWellSpacedSelection n χ σ τ H K) s).time| := by
  exact (Classical.choose_spec
    (exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
      (cglZeroDensityVerticalWindowNaturalLocalCapacity n χ σ τ H K))).2 r s hrs

end RHTower
