import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Coordinate-grid overlap bounds

This file extracts the finite-product counting mechanism of Lemma 6.3 in the supplied
Navier--Stokes paper. If every coordinate has at most `C` locally relevant grid positions, an
arbitrary relevance predicate selects at most `C ^ d` labels. The paper's two pulse signs give the
explicit three-dimensional bound `2 * C ^ 3`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.NavierStokesGridOverlap

noncomputable section

variable {α : Type*}

/-- All grid labels whose coordinates lie in their one-dimensional candidate sets. -/
noncomputable def coordinateGridLabels {d : ℕ} (A : Fin d → Finset α) :
    Finset (Fin d → α) :=
  Fintype.piFinset A

@[simp] theorem mem_coordinateGridLabels {d : ℕ} (A : Fin d → Finset α)
    (x : Fin d → α) :
    x ∈ coordinateGridLabels A ↔ ∀ i, x i ∈ A i := by
  simp [coordinateGridLabels]

@[simp] theorem card_coordinateGridLabels {d : ℕ} (A : Fin d → Finset α) :
    (coordinateGridLabels A).card = ∏ i, (A i).card := by
  simp [coordinateGridLabels]

/-- Any relevance predicate cuts out at most the full coordinatewise grid. -/
theorem card_relevant_coordinateGridLabels_le {d C : ℕ}
    (A : Fin d → Finset α) (relevant : (Fin d → α) → Prop)
    [DecidablePred relevant] (hA : ∀ i, (A i).card ≤ C) :
    ((coordinateGridLabels A).filter relevant).card ≤ C ^ d := by
  calc
    ((coordinateGridLabels A).filter relevant).card ≤ (coordinateGridLabels A).card :=
      card_filter_le _ _
    _ = ∏ i, (A i).card := card_coordinateGridLabels A
    _ ≤ ∏ _i : Fin d, C := by
      exact Finset.prod_le_prod' (fun i _hi ↦ hA i)
    _ = C ^ d := by simp

/-- Add the two pulse signs used by the paper without changing coordinate overlap. -/
noncomputable def signedCoordinateGridLabels {d : ℕ} (A : Fin d → Finset α) :
    Finset (Fin 2 × (Fin d → α)) :=
  Finset.univ ×ˢ coordinateGridLabels A

@[simp] theorem card_signedCoordinateGridLabels {d : ℕ} (A : Fin d → Finset α) :
    (signedCoordinateGridLabels A).card = 2 * ∏ i, (A i).card := by
  simp [signedCoordinateGridLabels]

theorem card_relevant_signed_coordinateGridLabels_le {d C : ℕ}
    (A : Fin d → Finset α) (relevant : (Fin 2 × (Fin d → α)) → Prop)
    [DecidablePred relevant] (hA : ∀ i, (A i).card ≤ C) :
    ((signedCoordinateGridLabels A).filter relevant).card ≤ 2 * C ^ d := by
  calc
    ((signedCoordinateGridLabels A).filter relevant).card ≤
        (signedCoordinateGridLabels A).card := card_filter_le _ _
    _ = 2 * ∏ i, (A i).card := card_signedCoordinateGridLabels A
    _ ≤ 2 * ∏ _i : Fin d, C :=
      Nat.mul_le_mul_left 2 (Finset.prod_le_prod' fun i _hi ↦ hA i)
    _ = 2 * C ^ d := by simp

/-- Lemma 6.3's pointwise overlap count: three coordinate grids and two signs give `2 C³`. -/
theorem card_relevant_signed_threeGridLabels_le (A : Fin 3 → Finset α)
    (relevant : (Fin 2 × (Fin 3 → α)) → Prop) [DecidablePred relevant]
    {C : ℕ} (hA : ∀ i, (A i).card ≤ C) :
    ((signedCoordinateGridLabels A).filter relevant).card ≤ 2 * C ^ 3 := by
  exact card_relevant_signed_coordinateGridLabels_le A relevant hA

/-- Along one radial line only one coordinate grid varies, so two signs give `2 C`. -/
theorem card_relevant_signed_oneGridLabels_le (A : Fin 1 → Finset α)
    (relevant : (Fin 2 × (Fin 1 → α)) → Prop) [DecidablePred relevant]
    {C : ℕ} (hA : ∀ i, (A i).card ≤ C) :
    ((signedCoordinateGridLabels A).filter relevant).card ≤ 2 * C := by
  simpa using card_relevant_signed_coordinateGridLabels_le A relevant hA

end

end GaloisForLFunctions.HTGeometry.NavierStokesGridOverlap
