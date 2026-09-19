import GaloisForLFunctions.RHTower.MaassFiniteDeckDirichletIntegrationByParts

/-!
# Central descent of the finite-deck Maass Dirichlet form

The action of `-1 : SL(2, ℤ)` on the upper half plane is trivial.  An
`SL(2, ℤ)`-equivariant finite-deck field consequently takes values in the
fixed sector of the central deck action.  This file realizes that sector as a
closed `L²` subspace and proves that the completed Dirichlet form, including
every exceptional Maass source, lands there injectively.

This corrects the Hilbert carrier for the forthcoming density and compactness
theorems: density in the whole regular-deck `L²` space is generally false.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ContDiff
namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open GaloisForLFunctions.HTGeometry SelbergMaassCongruenceTrace MaassCongruenceL2
noncomputable section

/-- The regular deck action of the central element represented by `-1`. -/
def deckCentralCoeff (N : ℕ) : DeckSpace N →L[ℂ] DeckSpace N :=
  ContinuousLinearEquiv.toContinuousLinearMap
    (LinearIsometryEquiv.toContinuousLinearEquiv
      (finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)))

/-- The central regular action on finite-deck `L²` vectors. -/
def deckCentralL2 (N : ℕ) : DeckL2 N →L[ℂ] DeckL2 N :=
  (deckCentralCoeff N).compLpL 2 cellMeasure

/-- The closed finite-deck `L²` sector compatible with the projective action
on the upper half plane. -/
def deckCentralFixedL2 (N : ℕ) : Submodule ℂ (DeckL2 N) :=
  (deckCentralL2 N - ContinuousLinearMap.id ℂ (DeckL2 N)).ker

private theorem neg_one_smul_eq (z : ℍ) : (-1 : SL2Z) • z = z := by
  have h := SL_neg_smul (g := (1 : SL2Z)) (z := z)
  simpa only [one_smul] using h

/-- The value coordinate of every finite-deck form pre-vector is fixed by the
central deck action. -/
theorem deckCentralL2_toDeckL2_of_formPreDomain (N : ℕ) (F : formPreDomain N) :
    deckCentralL2 N (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F)) =
      toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F) := by
  apply Lp.ext
  filter_upwards [
    (deckCentralCoeff N).coeFn_compLpL
      (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F)),
    MemLp.coeFn_toLp (formPreDomain.memLp F)] with z hcentral hF
  change (((deckCentralCoeff N).compLpL 2 cellMeasure)
      (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F))) z =
    (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F)) z
  rw [hcentral]
  change (deckCentralCoeff N) ((MemLp.toLp (F : ℍ → DeckSpace N)
    (formPreDomain.memLp F)) z) =
    (MemLp.toLp (F : ℍ → DeckSpace N) (formPreDomain.memLp F)) z
  rw [hF]
  change finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
    ((F : ℍ → DeckSpace N) z) = (F : ℍ → DeckSpace N) z
  calc
    finiteRegularUnitary (QuotientGroup.mk (-1 : SL2Z) : Deck N)
        ((F : ℍ → DeckSpace N) z) = (F : ℍ → DeckSpace N) ((-1 : SL2Z) • z) :=
      (formPreDomain.equivariant F (-1) z).symm
    _ = (F : ℍ → DeckSpace N) z := by rw [neg_one_smul_eq]

/-- The central defect of the value coordinate of a finite-deck form triple. -/
def deckCentralDefect (N : ℕ) : FormTriple N →L[ℂ] DeckL2 N :=
  (deckCentralL2 N - ContinuousLinearMap.id ℂ (DeckL2 N)).comp
    (PiLp.proj 2 (fun _ : Fin 3 => DeckL2 N) 0)

theorem deckCentralDefect_formEmbeddingMap (N : ℕ) (F : formPreDomain N) :
    deckCentralDefect N (formEmbeddingMap N F) = 0 := by
  change deckCentralL2 N (toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F)) -
    toDeckL2 (F : ℍ → DeckSpace N) (formPreDomain.memLp F) = 0
  rw [deckCentralL2_toDeckL2_of_formPreDomain]
  exact sub_self _

/-- Central fixedness persists under the three-coordinate form completion. -/
theorem formDomainClosure_le_deckCentralDefect_ker (N : ℕ) :
    formDomainClosure N ≤ (deckCentralDefect N).ker := by
  refine Submodule.topologicalClosure_minimal _ ?_ (deckCentralDefect N).isClosed_ker
  rintro _ ⟨F, rfl⟩
  exact deckCentralDefect_formEmbeddingMap N F

/-- The value coordinate of every completed finite-deck form vector is central-fixed. -/
theorem formInclusion_deckCentral_fixed (N : ℕ) (v : FormDomain N) :
    deckCentralL2 N (formInclusion N v) = formInclusion N v := by
  have hv := formDomainClosure_le_deckCentralDefect_ker N v.property
  change deckCentralDefect N (v : FormTriple N) = 0 at hv
  change deckCentralL2 N (formInclusion N v) - formInclusion N v = 0 at hv
  exact sub_eq_zero.mp hv

/-- The finite-deck form inclusion with its correct central-fixed codomain. -/
def formInclusionCentral (N : ℕ) : FormDomain N →L[ℂ] deckCentralFixedL2 N :=
  (formInclusion N).codRestrict (deckCentralFixedL2 N) fun v => by
    change deckCentralL2 N (formInclusion N v) - formInclusion N v = 0
    exact sub_eq_zero.mpr (formInclusion_deckCentral_fixed N v)

/-- Passing to the correct central-fixed carrier preserves the already-proved
closability of the completed form. -/
theorem formInclusionCentral_injective (N : ℕ) : Function.Injective (formInclusionCentral N) := by
  intro v w h
  apply formInclusion_injective N
  exact congrArg Subtype.val h

section Exceptional
variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)

/-- The actual exceptional source belongs to the central-fixed `L²` carrier. -/
def sourceCentralL2 : deckCentralFixedL2 N :=
  formInclusionCentral N
    (sourceFormVector N lam f)

theorem coe_sourceCentralL2 :
    (sourceCentralL2 N lam f : DeckL2 N) = sourceLp N f := by
  change formInclusion N (sourceFormVector N lam f) = sourceLp N f
  exact formInclusion_sourceFormVector N lam f

end Exceptional
end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
