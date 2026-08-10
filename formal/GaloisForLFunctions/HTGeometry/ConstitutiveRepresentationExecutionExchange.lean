import GaloisForLFunctions.HTGeometry.ConstitutiveDiagonalLawGenesis
import GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion

/-!
# Representation--execution exchange

Representation birth and operational novelty are independent.  Operational novelty is exactly
the splitting of an existing row-profile fibre, equivalently strict contraction of the invisible
intervention doctrine.  The complemented diagonal is operationally effective precisely when the
diagonal varies inside one row-profile fibre.  In particular every finite strict-order diagonal
stage has an unrepresented complemented diagonal which is nevertheless operationally inert.

All declarations are source-independent.  No RH or route premise occurs.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

namespace RepresentationExecutionExchange

/-- Complete row-profile reporter of a Boolean self-evaluator. -/
def evaluatorRowReporter {X : Type u} (E : BooleanSelfEvaluator X) : X → (X → Bool) :=
  fun x y ↦ E x y

/-- A challenge is represented when it is already an evaluator row. -/
def ReporterRepresented {X : Type u} (E : BooleanSelfEvaluator X) (c : X → Bool) : Prop :=
  ∃ a, evaluatorRowReporter E a = c

/-- Operational inertness is fibrewise descent through the complete row profile. -/
def ReporterOperationallyInert {X : Type u}
    (E : BooleanSelfEvaluator X) (c : X → Bool) : Prop :=
  ReporterDeterminedBy (evaluatorRowReporter E) c

/-- Operational effectiveness is failure of fibrewise descent through the complete row profile. -/
def ReporterOperationallyEffective {X : Type u}
    (E : BooleanSelfEvaluator X) (c : X → Bool) : Prop :=
  ¬ ReporterOperationallyInert E c

/-- **Fibre-splitting criterion.** A challenge is operationally effective exactly when it
separates two states having the same complete row profile. -/
theorem operationallyEffective_iff_fibre_split {X : Type u}
    (E : BooleanSelfEvaluator X) (c : X → Bool) :
    ReporterOperationallyEffective E c ↔
      ∃ x y, (∀ z, E x z = E y z) ∧ c x ≠ c y := by
  constructor
  · intro h
    unfold ReporterOperationallyEffective ReporterOperationallyInert ReporterDeterminedBy at h
    push Not at h
    obtain ⟨x, y, hrow, hc⟩ := h
    exact ⟨x, y, fun z ↦ congrFun hrow z, hc⟩
  · rintro ⟨x, y, hrow, hc⟩ hdescent
    exact hc (hdescent (funext hrow))

/-- **Execution exchange criterion.** Operational novelty is exactly strict contraction of the
old invisible-intervention doctrine after pairing in the challenge. -/
theorem operationallyEffective_iff_invisible_intervention {X : Type u}
    (E : BooleanSelfEvaluator X) (c : X → Bool) :
    ReporterOperationallyEffective E c ↔
      ∃ a : X → X,
        ReporterInvisible (evaluatorRowReporter E) a ∧
          ¬ ReporterInvisible (pairedReporter (evaluatorRowReporter E) c) a := by
  unfold ReporterOperationallyEffective ReporterOperationallyInert
  exact (pairedReporter_strict_contraction_iff (evaluatorRowReporter E) c).symm

/-- The anti-diagonal is effective exactly when diagonal values vary inside a row-profile fibre. -/
theorem antiDiagonal_operationallyEffective_iff {X : Type u}
    (E : BooleanSelfEvaluator X) :
    ReporterOperationallyEffective E (evaluatorAntiDiagonal E) ↔
      ∃ x y, (∀ z, E x z = E y z) ∧ E x x ≠ E y y := by
  rw [operationallyEffective_iff_fibre_split]
  constructor
  · rintro ⟨x, y, hrow, hanti⟩
    refine ⟨x, y, hrow, ?_⟩
    intro hdiag
    apply hanti
    exact congrArg (fun b : Bool ↦ !b) hdiag
  · rintro ⟨x, y, hrow, hdiag⟩
    refine ⟨x, y, hrow, ?_⟩
    intro hanti
    exact hdiag (Bool.not_injective hanti)

/-- The anti-diagonal is never represented by an existing evaluator row. -/
theorem antiDiagonal_not_represented {X : Type u} (E : BooleanSelfEvaluator X) :
    ¬ ReporterRepresented E (evaluatorAntiDiagonal E) := by
  rintro ⟨a, ha⟩
  exact evaluatorAntiDiagonal_ne_row E a ha

/-- An injective older reporter determines every challenge. -/
theorem reporterDeterminedBy_of_injective
    {X : Type u} {Y : Type v} (q : X → Y) (hq : Function.Injective q) (c : X → Bool) :
    ReporterDeterminedBy q c := by
  intro x y hxy
  exact congrArg c (hq hxy)

/-- A faithful row profile makes every challenge operationally inert. -/
theorem everyReporter_inert_of_rowReporter_injective {X : Type u}
    (E : BooleanSelfEvaluator X) (hE : Function.Injective (evaluatorRowReporter E))
    (c : X → Bool) :
    ReporterOperationallyInert E c :=
  reporterDeterminedBy_of_injective (evaluatorRowReporter E) hE c

/-- Two-state projection evaluator: both rows are the identity reporter. -/
def projectionEvaluator : BooleanSelfEvaluator Bool :=
  fun _ y ↦ y

/-- Identity challenge on the projection evaluator. -/
def identityBoolChallenge : Bool → Bool := id

theorem projection_identity_represented :
    ReporterRepresented projectionEvaluator identityBoolChallenge := by
  refine ⟨false, ?_⟩
  funext y
  rfl

theorem projection_identity_effective :
    ReporterOperationallyEffective projectionEvaluator identityBoolChallenge := by
  rw [operationallyEffective_iff_fibre_split]
  exact ⟨false, true, fun _ ↦ rfl, by simp [identityBoolChallenge]⟩

theorem projection_antiDiagonal_effective :
    ReporterOperationallyEffective projectionEvaluator
      (evaluatorAntiDiagonal projectionEvaluator) := by
  rw [antiDiagonal_operationallyEffective_iff]
  exact ⟨false, true, fun _ ↦ rfl, by simp [projectionEvaluator]⟩

/-- Equal strict-order rows on a finite ordinal have equal row indices. -/
theorem finiteDiagonalRowReporter_injective (n : ℕ) :
    Function.Injective (evaluatorRowReporter (finiteDiagonalEvaluator n)) := by
  intro i j hij
  apply le_antisymm
  · by_contra hle
    have hlt : j < i := lt_of_not_ge hle
    have hv := congrFun hij j
    simp [evaluatorRowReporter, finiteDiagonalEvaluator, hlt] at hv
  · by_contra hle
    have hlt : i < j := lt_of_not_ge hle
    have hv := congrFun hij i
    simp [evaluatorRowReporter, finiteDiagonalEvaluator, hlt] at hv

/-- Every challenge at a finite strict-order stage is operationally inert. -/
theorem finiteDiagonal_everyReporter_inert (n : ℕ) (c : Fin n → Bool) :
    ReporterOperationallyInert (finiteDiagonalEvaluator n) c :=
  everyReporter_inert_of_rowReporter_injective
    (finiteDiagonalEvaluator n) (finiteDiagonalRowReporter_injective n) c

/-- First row challenge in the two-state strict-order evaluator. -/
def strictOrderFirstRow : Fin 2 → Bool :=
  evaluatorRowReporter (finiteDiagonalEvaluator 2) 0

theorem strictOrder_firstRow_represented :
    ReporterRepresented (finiteDiagonalEvaluator 2) strictOrderFirstRow :=
  ⟨0, rfl⟩

theorem strictOrder_firstRow_inert :
    ReporterOperationallyInert (finiteDiagonalEvaluator 2) strictOrderFirstRow :=
  finiteDiagonal_everyReporter_inert 2 strictOrderFirstRow

theorem strictOrder_antiDiagonal_inert :
    ReporterOperationallyInert (finiteDiagonalEvaluator 2)
      (evaluatorAntiDiagonal (finiteDiagonalEvaluator 2)) :=
  finiteDiagonal_everyReporter_inert 2 (evaluatorAntiDiagonal (finiteDiagonalEvaluator 2))

/-- All four represented/unrepresented and effective/inert chambers occur on two-state
evaluators. -/
theorem four_representation_execution_chambers :
    (ReporterRepresented projectionEvaluator identityBoolChallenge ∧
      ReporterOperationallyEffective projectionEvaluator identityBoolChallenge) ∧
    (¬ ReporterRepresented projectionEvaluator (evaluatorAntiDiagonal projectionEvaluator) ∧
      ReporterOperationallyEffective projectionEvaluator
        (evaluatorAntiDiagonal projectionEvaluator)) ∧
    (ReporterRepresented (finiteDiagonalEvaluator 2) strictOrderFirstRow ∧
      ReporterOperationallyInert (finiteDiagonalEvaluator 2) strictOrderFirstRow) ∧
    (¬ ReporterRepresented (finiteDiagonalEvaluator 2)
        (evaluatorAntiDiagonal (finiteDiagonalEvaluator 2)) ∧
      ReporterOperationallyInert (finiteDiagonalEvaluator 2)
        (evaluatorAntiDiagonal (finiteDiagonalEvaluator 2))) := by
  exact ⟨
    ⟨projection_identity_represented, projection_identity_effective⟩,
    ⟨antiDiagonal_not_represented projectionEvaluator, projection_antiDiagonal_effective⟩,
    ⟨strictOrder_firstRow_represented, strictOrder_firstRow_inert⟩,
    ⟨antiDiagonal_not_represented (finiteDiagonalEvaluator 2),
      strictOrder_antiDiagonal_inert⟩⟩

/-- Complete representation--execution exchange statement at one finite diagonal stage. -/
def FiniteDiagonalExchangeLaw (n : ℕ) : Prop :=
    Function.Injective (evaluatorRowReporter (finiteDiagonalEvaluator n)) ∧
    ¬ ReporterRepresented (finiteDiagonalEvaluator n)
      (evaluatorAntiDiagonal (finiteDiagonalEvaluator n)) ∧
    ReporterOperationallyInert (finiteDiagonalEvaluator n)
      (evaluatorAntiDiagonal (finiteDiagonalEvaluator n)) ∧
    ¬ ∃ a : Fin n → Fin n,
      ReporterInvisible (evaluatorRowReporter (finiteDiagonalEvaluator n)) a ∧
        ¬ ReporterInvisible
          (pairedReporter (evaluatorRowReporter (finiteDiagonalEvaluator n))
            (evaluatorAntiDiagonal (finiteDiagonalEvaluator n))) a

/-- Every finite diagonal-genesis stage has an injective row profile and an unrepresented but
operationally inert anti-diagonal; adjoining it cannot contract invisible interventions. -/
theorem finiteDiagonal_unrepresented_inert_no_contraction (n : ℕ) :
    FiniteDiagonalExchangeLaw n := by
  unfold FiniteDiagonalExchangeLaw
  have hinert := finiteDiagonal_everyReporter_inert n
    (evaluatorAntiDiagonal (finiteDiagonalEvaluator n))
  refine ⟨finiteDiagonalRowReporter_injective n,
    antiDiagonal_not_represented (finiteDiagonalEvaluator n), hinert, ?_⟩
  intro hcontraction
  exact (pairedReporter_strict_contraction_iff
    (evaluatorRowReporter (finiteDiagonalEvaluator n))
    (evaluatorAntiDiagonal (finiteDiagonalEvaluator n))).1 hcontraction hinert

/-- Closed capstone: both independence chambers and diagonal inertness hold unconditionally. -/
theorem representationExecutionExchange_closed :
    (ReporterRepresented projectionEvaluator identityBoolChallenge ∧
      ReporterOperationallyEffective projectionEvaluator identityBoolChallenge) ∧
    (¬ ReporterRepresented projectionEvaluator (evaluatorAntiDiagonal projectionEvaluator) ∧
      ReporterOperationallyEffective projectionEvaluator
        (evaluatorAntiDiagonal projectionEvaluator)) ∧
    (ReporterRepresented (finiteDiagonalEvaluator 2) strictOrderFirstRow ∧
      ReporterOperationallyInert (finiteDiagonalEvaluator 2) strictOrderFirstRow) ∧
    (¬ ReporterRepresented (finiteDiagonalEvaluator 2)
        (evaluatorAntiDiagonal (finiteDiagonalEvaluator 2)) ∧
      ReporterOperationallyInert (finiteDiagonalEvaluator 2)
        (evaluatorAntiDiagonal (finiteDiagonalEvaluator 2))) ∧
    ∀ n, FiniteDiagonalExchangeLaw n := by
  exact ⟨four_representation_execution_chambers.1,
    four_representation_execution_chambers.2.1,
    four_representation_execution_chambers.2.2.1,
    four_representation_execution_chambers.2.2.2,
    finiteDiagonal_unrepresented_inert_no_contraction⟩

end RepresentationExecutionExchange

end GaloisForLFunctions.HTGeometry
