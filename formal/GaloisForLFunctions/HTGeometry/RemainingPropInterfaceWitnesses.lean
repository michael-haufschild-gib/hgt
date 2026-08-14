import GaloisForLFunctions.HTGeometry.ElementaryStokesRecognitionComplexity
import GaloisForLFunctions.HTGeometry.ReplicaHistoryFactorizationLaw
import GaloisForLFunctions.HTGeometry.ProjectiveRecurrenceProtectionLaw
import GaloisForLFunctions.HTGeometry.CompletionKernelPairTransversalityLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveSemanticTransportArityPromotion
import GaloisForLFunctions.HTGeometry.GammaPoleMovingAffineProfileHorizon
import GaloisForLFunctions.HTGeometry.ObserverActionRecurrenceProjectionLaw
import GaloisForLFunctions.HTGeometry.TemporalPhaseValuationTomographyLaw
import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail
import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect

/-!
# Remaining proposition-interface witnesses

Explicit realizations for relation, observation, support, phase, Gamma-profile, tail, and boundary
interfaces whose canonical inhabitants were previously hidden behind subtype instances or
equivalence criteria.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Rearrangement is reflexive for every finite history. -/
theorem isHistoryRearrangement_refl
    {R A : Type*} [Fintype R] [DecidableEq A] (x : R → A) :
    IsHistoryRearrangement x x := by
  intro a
  rfl

/-- Componentwise rearrangement is reflexive for every joint finite history. -/
theorem isComponentHistoryRearrangement_refl
    {C R : Type*} [Fintype R]
    {I : C → Type*} [∀ c, DecidableEq (I c)]
    (x : R → ∀ c, I c) :
    IsComponentHistoryRearrangement x x := by
  intro c
  exact isHistoryRearrangement_refl _

/-- The zero projective character is robust under every declared perturbation family. -/
theorem robustProjectiveRelation_zero
    {I : Type*} (energy : I → ℝ) (allowed : Set (I → ℝ)) :
    RobustProjectiveRelation energy allowed (0 : ProjectiveCharacter I) := by
  intro w hw
  simp [projectiveCharacterDetuning]

/-- One identity channel recovers every target observable. -/
theorem observationFamilyRecovers_identity
    {X C : Type*} (χ : X → C) :
    ObservationFamilyRecovers (Y := fun _ : Unit => X) (fun _ x => x) χ := by
  intro x y hxy
  exact congrArg χ (hxy Unit.unit)

/-- The empty family of reported supports is permutation-closed. -/
theorem supportReporterDoctrine_empty
    {I : Type*} [Fintype I] [DecidableEq I] :
    SupportReporterDoctrine (∅ : Set (Finset I)) := by
  intro e S hS
  exact hS.elim

/-- The universal family of reported supports is permutation-closed. -/
theorem supportReporterDoctrine_univ
    {I : Type*} [Fintype I] [DecidableEq I] :
    SupportReporterDoctrine (Set.univ : Set (Finset I)) := by
  intro e S hS
  exact Set.mem_univ _

/-- The zero moving Gamma source has no outer poles, hence in particular at most simple poles. -/
theorem gammaPoleProfileAtMostSimple_zero (n : ℕ) :
    GammaPoleProfileAtMostSimple n
      (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) := by
  have hzero : GammaPoleProfilePoleGradeAtMost n 0
      (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :=
    (gammaPoleProfilePoleGradeAtMost_zero_iff_constant
      (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))).2 ⟨0, by simp⟩
  intro q hq
  exact hzero q (by omega)

/-- A finite-torus phase law unlocks a character exactly as soon as its sinc argument is nonzero. -/
theorem phaseLawCharacterUnlocked_finiteTorus_of_detuning
    {d : Type*} [Fintype d]
    (k : ProjectiveCharacter d) (omega : d → ℝ) (A : ℝ)
    (hdetuning : A * finiteProjectiveCharacterDetuning k omega ≠ 0) :
    PhaseLawCharacterUnlocked (finiteTorusPhaseProbabilityMeasure omega A) k := by
  unfold PhaseLawCharacterUnlocked
  change finiteProjectivePhaseCoefficient k omega A ≠ 1
  rw [finiteProjectivePhaseCoefficient_eq_sinc]
  exact_mod_cast real_sinc_ne_one_of_ne_zero hdetuning

/-- Every nonzero observed energy gap gives an explicitly unlocked ordered-pair character. -/
theorem phaseLawCharacterUnlocked_pair
    {d : Type*} [Fintype d] (i j : d) (omega : d → ℝ) (A : ℝ)
    (hgap : A * (omega i - omega j) ≠ 0) :
    PhaseLawCharacterUnlocked (finiteTorusPhaseProbabilityMeasure omega A)
      (pairProjectiveCharacter i j) := by
  apply phaseLawCharacterUnlocked_finiteTorus_of_detuning
  rwa [finiteProjectiveCharacterDetuning_pair]

/-- With no source columns, every finite shift-jet rectangle has full tail rank. -/
theorem completeShiftJetTailIndependent_empty_source
    {A P : Type*} [Fintype A]
    (factor : A → P → ℂ) (clock : P → ℂ) :
    CompleteShiftJetTailIndependent (fun i : Empty => i.elim) factor clock := by
  intro m c hc
  funext i
  exact i.1.elim

/-- Identity transport creates no boundary escape. -/
theorem BoundaryMigration.escapeFree_id
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (J : Submodule 𝕜 V) :
    BoundaryMigration.EscapeFree (LinearMap.id (R := 𝕜) (M := V)) J J := by
  simp [BoundaryMigration.EscapeFree]

/-- Identity transport creates no boundary deficit. -/
theorem BoundaryMigration.deficitFree_id
    {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (J : Submodule 𝕜 V) :
    BoundaryMigration.DeficitFree (LinearMap.id (R := 𝕜) (M := V)) J J := by
  simp [BoundaryMigration.DeficitFree]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.IrregularStokes.ElementaryDecoratedGraph

/-- There are no pair queries on the empty Stokes graph. -/
theorem pairQueryHolds_empty
    (g : ElementaryDecoratedGraph 0) (q : PairRecognitionQuery 0) :
    g.pairQueryHolds q :=
  Fin.elim0 q.1

/-- There are no triangle queries on the empty Stokes graph. -/
theorem triangleQueryHolds_empty
    (g : ElementaryDecoratedGraph 0) (q : TriangleRecognitionQuery 0) :
    g.triangleQueryHolds q :=
  Fin.elim0 q.1

end GaloisForLFunctions.IrregularStokes.ElementaryDecoratedGraph
