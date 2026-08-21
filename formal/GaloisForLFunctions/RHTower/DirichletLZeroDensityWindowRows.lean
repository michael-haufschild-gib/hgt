/-
# CGL character rows from spaced Dirichlet-L zero copies

This module maps the finite, multiplicity-aware, well-spaced zero-copy packet
into the exact character/ordinate row carrier used by the Chen--Gupta--Li
class-I and class-II large-value machinery.  The selected rows retain their
common primitive character, their local vertical window, and their certified
ordinate separation.

No RH, GRH, zero-detection premise, local zero-density estimate, or
large-value bound is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowSpacing
import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues

noncomputable section

namespace RHTower

/-- The CGL character/ordinate row carried by one centered-window
multiplicity-copy zero label. -/
def cglZeroDensityVerticalWindowCopyRow
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :
    CGLCharacterDyadicRowData (n + 1) :=
  { time := cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r
    character := χ.1 }

/-- Every zero-copy ordinate lies in its original centered vertical window. -/
theorem cglZeroDensityVerticalWindowCopyOrdinate_mem_window
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :
    |cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r - τ| ≤ H := by
  unfold cglZeroDensityVerticalWindowCopyOrdinate
  exact (cglZeroDensityVerticalWindowZeroSupport_subset_window n χ σ τ H
    ((Fintype.equivFin (CGLZeroDensityVerticalWindowZeroCopy n χ σ τ H)).symm r).1.2).2.2

/-- The row time inherits the centered-window bound. -/
theorem cglZeroDensityVerticalWindowCopyRow_time_mem_window
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :
    |(cglZeroDensityVerticalWindowCopyRow n χ σ τ H r).time - τ| ≤ H := by
  exact cglZeroDensityVerticalWindowCopyOrdinate_mem_window n χ σ τ H r

/-- Every zero-copy row has the fixed Dirichlet character of its source
window. -/
theorem cglZeroDensityVerticalWindowCopyRow_character
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :
    (cglZeroDensityVerticalWindowCopyRow n χ σ τ H r).character = χ.1 := rfl

/-- CGL rows indexed by the finite selected zero-copy subpacket. -/
def cglZeroDensityVerticalWindowSelectedRows
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))) :
    Fin (Fintype.card (↑S)) → CGLCharacterDyadicRowData (n + 1) :=
  fun r => cglZeroDensityVerticalWindowCopyRow n χ σ τ H
    ((Fintype.equivFin (↑S)).symm r).1

/-- The actual completed-Dirichlet-L zero retained alongside a selected CGL
row. -/
def cglZeroDensityVerticalWindowSelectedRowsPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)))
    (r : Fin (Fintype.card (↑S))) : CGLZeroDensityVerticalWindowZero n χ σ τ H :=
  cglZeroDensityVerticalWindowCopyPoint n χ σ τ H
    ((Fintype.equivFin (↑S)).symm r).1

/-- A selected CGL row is accompanied by an actual completed Dirichlet-L
zero, with no analytic assumption supplied by callers. -/
theorem cglZeroDensityVerticalWindowSelectedRowsPoint_isZero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)))
    (r : Fin (Fintype.card (↑S))) :
    DirichletCharacter.completedLFunction χ.1
      (cglZeroDensityVerticalWindowSelectedRowsPoint n χ σ τ H S r).1 = 0 :=
  cglZeroDensityVerticalWindowCopyPoint_isZero n χ σ τ H
    ((Fintype.equivFin (↑S)).symm r).1

/-- The companion zero's ordinate is exactly the time stored in its CGL row. -/
theorem cglZeroDensityVerticalWindowSelectedRowsPoint_im_eq_time
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)))
    (r : Fin (Fintype.card (↑S))) :
    (cglZeroDensityVerticalWindowSelectedRowsPoint n χ σ τ H S r).1.im =
      (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S r).time := rfl

/-- Selected CGL rows remain inside the original local vertical window. -/
theorem cglZeroDensityVerticalWindowSelectedRows_time_mem_window
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)))
    (r : Fin (Fintype.card (↑S))) :
    |(cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S r).time - τ| ≤ H := by
  unfold cglZeroDensityVerticalWindowSelectedRows
  exact cglZeroDensityVerticalWindowCopyRow_time_mem_window n χ σ τ H
    ((Fintype.equivFin (↑S)).symm r).1

/-- All selected CGL rows carry the same source character. -/
theorem cglZeroDensityVerticalWindowSelectedRows_character
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)))
    (r : Fin (Fintype.card (↑S))) :
    (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S r).character = χ.1 := by
  rfl

/-- A separated selection of zero copies gives equally separated CGL row
ordinates. -/
theorem cglZeroDensityVerticalWindowSelectedRows_separated
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (C : CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)))
    (hS : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → C.spacing ≤
      |cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r -
        cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H s|)
    (r s : Fin (Fintype.card (↑S))) (hrs : r ≠ s) :
    C.spacing ≤ |(cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S r).time -
      (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S s).time| := by
  let e := Fintype.equivFin (↑S)
  let a := e.symm r
  let b := e.symm s
  have hab : a.1 ≠ b.1 := by
    intro heq
    have hab' : a = b := Subtype.ext heq
    apply hrs
    simpa only [a, b, e.apply_symm_apply] using congrArg e hab'
  have hsep := hS a.1 a.2 b.1 b.2 hab
  simpa only [cglZeroDensityVerticalWindowSelectedRows,
    cglZeroDensityVerticalWindowCopyRow] using hsep

/-- The local-count saturation theorem supplies a separated finite CGL row
packet controlling the literal multiplicity-weighted zero count. -/
theorem exists_cglZeroDensityVerticalWindowSelectedRows_wellSpaced_count
    {n : ℕ} {χ : NonprincipalDirichletCharacter n} {σ τ : ℝ} {H : NNReal}
    (C : CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H) :
    ∃ S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)),
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
        (2 * C.capacity * S.card : ℕ) ∧
        ∀ r s : Fin (Fintype.card (↑S)), r ≠ s → C.spacing ≤
          |(cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S r).time -
            (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S s).time| := by
  rcases exists_cglZeroDensityVerticalWindowCopy_wellSpaced_count C with ⟨S, hcount, hsep⟩
  refine ⟨S, hcount, ?_⟩
  intro r s hrs
  exact cglZeroDensityVerticalWindowSelectedRows_separated n χ σ τ H C S hsep r s hrs

/-- The actual centered-window zero packet supplies unit-separated CGL rows
without caller-supplied capacity data.  The closed baseline uses the full
zero-copy cardinality as its explicit capacity. -/
theorem exists_cglZeroDensityVerticalWindowSelectedRows_unit_wellSpaced_count
    {n : ℕ} {χ : NonprincipalDirichletCharacter n} {σ τ : ℝ} {H : NNReal} :
    ∃ S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)),
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
        (2 * cglZeroDensityVerticalWindowCopyCard n χ σ τ H * S.card : ℕ) ∧
        ∀ r s : Fin (Fintype.card (↑S)), r ≠ s → (1 : ℝ) ≤
          |(cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S r).time -
            (cglZeroDensityVerticalWindowSelectedRows n χ σ τ H S s).time| := by
  rcases exists_cglZeroDensityVerticalWindowCopy_unit_wellSpaced_count
    (n := n) (χ := χ) (σ := σ) (τ := τ) (H := H) with ⟨S, hcount, hsep⟩
  refine ⟨S, hcount, ?_⟩
  intro r s hrs
  simpa [cglZeroDensityVerticalWindowUnitLocalCapacity] using
    cglZeroDensityVerticalWindowSelectedRows_separated n χ σ τ H
      (cglZeroDensityVerticalWindowUnitLocalCapacity n χ σ τ H) S hsep r s hrs

end RHTower
