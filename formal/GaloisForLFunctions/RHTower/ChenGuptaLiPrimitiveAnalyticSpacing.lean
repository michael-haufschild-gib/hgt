/-
# Chen--Gupta--Li primitive rows with analytic spacing capacity

This is the Section-12 primitive-character carrier built from the analytic
Jensen capacity rather than the tautological full-packet capacity.  It keeps
the literal primitive zero, CGL character/ordinate row, and arbitrary natural
spacing for each primitive character, then aggregates its exact selection
loss over the finite primitive family at one modulus.

The capacity remains character-dependent.  Thus this supplies the closed
analytic selection interface, not CGL's uniform `(qT)^ε log(qT)` selection
loss or its final density theorem.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveFamilyPackets
import GaloisForLFunctions.RHTower.DirichletLZeroDensityAnalyticSpacing

noncomputable section

namespace RHTower

/-- The analytic-capacity natural-scale selection at the CGL critical-line
threshold for one certified primitive nonprincipal character. -/
noncomputable def cglPrimitiveClassIAnalyticNaturalWellSpacedSelection
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ.1 (1 / 2) τ H)) :=
  cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K

/-- The closed Jensen capacity controls the literal multiplicity-weighted
critical-line window count through its canonical selected packet. -/
theorem cglPrimitiveClassIAnalyticNaturalWellSpacedSelection_count
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    completedLFunctionZeroDensityVerticalWindowCount n χ.1 (1 / 2) τ H ≤
      (2 * (cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity n χ.1 (1 / 2) τ H K).capacity *
        (cglPrimitiveClassIAnalyticNaturalWellSpacedSelection n χ τ H K).card : ℕ) := by
  exact cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection_count n χ.1 (1 / 2) τ H K

/-- An analytic-capacity selected zero which lies strictly right of the
critical line.  Its strict inequality is certified in the carrier. -/
def CGLPrimitiveClassIAnalyticNaturalWellSpacedIndex
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :=
  {r : Fin (Fintype.card (↑(cglPrimitiveClassIAnalyticNaturalWellSpacedSelection n χ τ H K))) //
    (1 / 2 : ℝ) <
      (cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
        (cglPrimitiveClassIAnalyticNaturalWellSpacedSelection n χ τ H K) r).1.re}

/-- The literal CGL character/ordinate row of one analytic-capacity selected
primitive zero. -/
def cglPrimitiveClassIAnalyticNaturalWellSpacedRow
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassIAnalyticNaturalWellSpacedIndex n χ τ H K) :
    CGLCharacterDyadicRowData (n + 1) :=
  cglZeroDensityVerticalWindowSelectedRows n χ.1 (1 / 2) τ H
    (cglPrimitiveClassIAnalyticNaturalWellSpacedSelection n χ τ H K) r.1

/-- The actual primitive Class-I window zero retained by one analytic-capacity
selected row. -/
def cglPrimitiveClassIAnalyticNaturalWellSpacedZero
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassIAnalyticNaturalWellSpacedIndex n χ τ H K) :
    CGLPrimitiveClassIWindowZero n χ τ H :=
  ⟨cglZeroDensityVerticalWindowSelectedRowsPoint n χ.1 (1 / 2) τ H
    (cglPrimitiveClassIAnalyticNaturalWellSpacedSelection n χ τ H K) r.1, r.2⟩

/-- Every analytic-capacity selected row retains its original primitive
character. -/
theorem cglPrimitiveClassIAnalyticNaturalWellSpacedRow_character
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassIAnalyticNaturalWellSpacedIndex n χ τ H K) :
    (cglPrimitiveClassIAnalyticNaturalWellSpacedRow n χ τ H K r).character = χ.1.1 := rfl

/-- The selected CGL row stores exactly the ordinate of its actual primitive
zero. -/
theorem cglPrimitiveClassIAnalyticNaturalWellSpacedZero_im_eq_row_time
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r : CGLPrimitiveClassIAnalyticNaturalWellSpacedIndex n χ τ H K) :
    (cglPrimitiveClassIAnalyticNaturalWellSpacedZero n χ τ H K r).1.1.im =
      (cglPrimitiveClassIAnalyticNaturalWellSpacedRow n χ τ H K r).time := rfl

/-- Distinct analytic-capacity primitive rows retain literal `K+1` ordinate
separation. -/
theorem cglPrimitiveClassIAnalyticNaturalWellSpacedRows_separated
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (r s : CGLPrimitiveClassIAnalyticNaturalWellSpacedIndex n χ τ H K) (hrs : r ≠ s) :
    (K + 1 : ℕ) ≤ |(cglPrimitiveClassIAnalyticNaturalWellSpacedRow n χ τ H K r).time -
      (cglPrimitiveClassIAnalyticNaturalWellSpacedRow n χ τ H K s).time| := by
  apply cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection_separated
    n χ.1 (1 / 2) τ H K r.1 s.1
  intro h
  exact hrs (Subtype.ext h)

/-- The aggregate analytic-spacing selection loss over every primitive
nonprincipal character at literal modulus `n+1`. -/
noncomputable def cglPrimitiveClassIAnalyticNaturalFamilySelectionLoss
    (n : ℕ) (τ : ℝ) (H : NNReal) (K : ℕ) : ℝ :=
  ∑ χ : CGLPrimitiveNonprincipalCharacterFamily n,
    (2 * (cglZeroDensityVerticalWindowAnalyticNaturalLocalCapacity n χ.1 (1 / 2) τ H K).capacity *
      (cglZeroDensityVerticalWindowAnalyticNaturalWellSpacedSelection n χ.1 (1 / 2) τ H K).card : ℕ)

/-- The exact primitive-family critical-line window count is controlled by
the sum of its internally certified analytic selection losses. -/
theorem cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount_le_analyticSelectionLoss
    (n : ℕ) (τ : ℝ) (H : NNReal) (K : ℕ) :
    cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount n (1 / 2) τ H ≤
      cglPrimitiveClassIAnalyticNaturalFamilySelectionLoss n τ H K := by
  unfold cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount
    cglPrimitiveClassIAnalyticNaturalFamilySelectionLoss
  exact Finset.sum_le_sum fun χ _ =>
    cglPrimitiveClassIAnalyticNaturalWellSpacedSelection_count n
      (cglPrimitiveNonprincipalCharacterFamily_asPrimitive χ) τ H K

end RHTower
