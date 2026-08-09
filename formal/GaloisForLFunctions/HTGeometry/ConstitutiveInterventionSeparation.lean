import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# Constitutive intervention separation

This module formalizes a closed process theorem: two directed constitutive systems have identical
complete passive endpoint maps, but a single marked intervention separates them exactly.  The
result has no probabilistic, positivity, topology, or arithmetic hypothesis; passive observation and
intervention are explicit finite functions.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Two opposite directed constitutive mechanisms. -/
inductive ConstitutiveBitDirection where
  | forward
  | backward
  deriving DecidableEq

/-- Before intervention both mechanisms expose the same endpoint pair `(u,u)`. -/
def constitutiveBitPassiveEndpoint
    (_ : ConstitutiveBitDirection) (u : Bool) : Bool × Bool :=
  (u, u)

/-- Complete passive record, retaining every exogenous input and both endpoints. -/
def constitutiveBitPassiveRecord
    (d : ConstitutiveBitDirection) : Bool → Bool × Bool :=
  constitutiveBitPassiveEndpoint d

/-- Observed `Y` after the marked intervention `do(X=false)`. -/
def constitutiveBitDoXFalseY
    (d : ConstitutiveBitDirection) (u : Bool) : Bool :=
  match d with
  | .forward => false
  | .backward => u

/-- Observed `X` after the marked intervention `do(Y=false)`. -/
def constitutiveBitDoYFalseX
    (d : ConstitutiveBitDirection) (u : Bool) : Bool :=
  match d with
  | .forward => u
  | .backward => false

/-- The complete passive records of the opposite mechanisms are definitionally equal. -/
theorem constitutiveBit_passive_records_equal :
    constitutiveBitPassiveRecord .forward = constitutiveBitPassiveRecord .backward := by
  rfl

/-- Every passive statistic agrees, even when it is allowed to inspect the exogenous input and both
endpoints. -/
theorem constitutiveBit_all_passive_statistics_equal :
    ∀ (α : Type) (f : Bool → (Bool × Bool) → α) (u : Bool),
      f u (constitutiveBitPassiveEndpoint .forward u) =
        f u (constitutiveBitPassiveEndpoint .backward u) := by
  intro α f u
  rfl

/-- No reader of the complete passive record can distinguish the mechanisms. -/
theorem constitutiveBit_no_passive_reader_separates :
    ∀ (α : Type) (reader : (Bool → Bool × Bool) → α),
      reader (constitutiveBitPassiveRecord .forward) =
        reader (constitutiveBitPassiveRecord .backward) := by
  intro α reader
  rw [constitutiveBit_passive_records_equal]

/-- `do(X=false)` separates the systems at the exogenous input `true`. -/
theorem constitutiveBit_doX_separates :
    constitutiveBitDoXFalseY .forward true ≠
      constitutiveBitDoXFalseY .backward true := by
  exact Bool.false_ne_true

/-- `do(Y=false)` separates them in the opposite direction. -/
theorem constitutiveBit_doY_separates :
    constitutiveBitDoYFalseX .forward true ≠
      constitutiveBitDoYFalseX .backward true := by
  intro h
  exact Bool.false_ne_true h.symm

/-- The full `do(X=false)` response record reconstructs the directed mechanism. -/
theorem constitutiveBit_doX_record_injective :
    Function.Injective (fun d ↦ constitutiveBitDoXFalseY d) := by
  intro d e h
  cases d <;> cases e
  · rfl
  · exfalso
    exact constitutiveBit_doX_separates (congrFun h true)
  · exfalso
    exact constitutiveBit_doX_separates (congrFun h true).symm
  · rfl

/-- **Passive/intervention strictness.** Passive observation is noninjective while one marked
intervention is injective on the same constitutive law space. -/
theorem constitutiveBit_passive_noninjective_and_intervention_injective :
    (¬ Function.Injective constitutiveBitPassiveRecord) ∧
      Function.Injective (fun d ↦ constitutiveBitDoXFalseY d) := by
  constructor
  · intro h
    have : ConstitutiveBitDirection.forward = ConstitutiveBitDirection.backward :=
      h constitutiveBit_passive_records_equal
    cases this
  · exact constitutiveBit_doX_record_injective

end GaloisForLFunctions.HTGeometry
