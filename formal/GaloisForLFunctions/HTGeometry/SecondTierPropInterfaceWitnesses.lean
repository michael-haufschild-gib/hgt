import GaloisForLFunctions.HTGeometry.PartialCompletionAdmissionSeparationLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveEntropicAlternatingFormation
import GaloisForLFunctions.HTGeometry.ActiveChargeRankHypertranscendence
import GaloisForLFunctions.HTGeometry.ConstitutiveReporterMeetPromotion
import GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal
import GaloisForLFunctions.HTGeometry.ConstitutiveFormationReporter
import GaloisForLFunctions.HTGeometry.ClockCapacityPacketBoundary
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.CoherentSourceFunctor
import GaloisForLFunctions.HTGeometry.SourcePointedExactDescentLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveLawSaturation
import GaloisForLFunctions.HTGeometry.ConstitutiveCarrierGenesisRepair
import GaloisForLFunctions.HTGeometry.MultipleGammaPeriodActionLawstack

/-!
# Canonical witnesses for the second tier of proposition-valued interfaces

These results discharge degenerate chambers uniformly and expose composition laws for the
interfaces that behave as relations.  They do not assume the interface propositions they prove.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Every partial completion recovers every constant target on its admitted domain. -/
theorem partialCompletion_recoversOnAdmitted_const
    {X Q C : Type*} (P : PartialCompletion X Q) (c : C) :
    P.RecoversOnAdmitted (fun _ => c) := by
  apply (partialCompletion_recoversOnAdmitted_iff_kernelRefines P _).2
  intro x y hxy
  rfl

/-- A constant history with zero action is an exact real-action repair step. -/
theorem isRealActionRepairStep_const_history_zero
    {S : Type*} (potential : S → ℝ) (s : S) (n : ℕ) :
    IsRealActionRepairStep potential (fun _ => s) (fun _ => 0) n := by
  simp [IsRealActionRepairStep]

/-- The zero phase has a bilinear charge factorization of every finite rank. -/
theorem bilinearChargeFactorization_zero (N : ℕ) :
    BilinearChargeFactorization (fun _ => 0) N := by
  refine ⟨fun _ _ => 0, fun _ _ => 0, ?_⟩
  simp

/-- Reporter refinement is reflexive. -/
theorem reporterRefines_refl {α β : Type*} (q : α → β) :
    ReporterRefines q q := by
  exact ⟨id, fun _ => rfl⟩

/-- Reporter refinement is transitive. -/
theorem reporterRefines_trans
    {α β γ δ : Type*} {coarse : α → β} {middle : α → γ} {fine : α → δ}
    (h₁ : ReporterRefines coarse middle) (h₂ : ReporterRefines middle fine) :
    ReporterRefines coarse fine := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  refine ⟨f ∘ g, ?_⟩
  intro x
  rw [hf, hg]
  rfl

/-- Every constant reporter is refined by every reporter on the same source. -/
theorem reporterRefines_const
    {α β γ : Type*} (b : β) (fine : α → γ) :
    ReporterRefines (fun _ => b) fine := by
  exact ⟨fun _ => b, fun _ => rfl⟩

/-- Removing the whole proof base succeeds exactly when the empty base does not derive the target. -/
theorem successfulKernelRevision_self_iff
    {α : Type*} [DecidableEq α] (C : FiniteConsequence α) (T : Finset α) (a : α) :
    SuccessfulKernelRevision C T a T ↔ a ∉ C.derive ∅ := by
  simp [SuccessfulKernelRevision]

/-- The coframe of all set-valued reporters separates every pair of source sets. -/
theorem formationReporterCoframeSeparates_univ
    {α : Type*} :
    FormationReporterCoframeSeparates (Set.univ : Set (Set α → Set α)) := by
  intro s t h
  simpa using h id (Set.mem_univ id)

/-- The zero finite-rank packet is coordinatewise square summable. -/
theorem packetMemℓp_zero (r : ℕ) :
    PacketMemℓp (fun _ : ℕ => fun _ : Fin r => 0) := by
  intro a
  change Memℓp (0 : ℕ → ℂ) 2
  exact zero_memℓp

namespace Interfinity

/-- The zero source family is a cocycle for every linear time family. -/
theorem isSourceCocycle_zero
    {Φ : Type*} [AddCommGroup Φ] [Module ℂ Φ]
    (S : NNReal → (Φ →ₗ[ℂ] Φ)) :
    IsSourceCocycle S (fun _ => 0) := by
  intro V W f
  simp

end Interfinity

/-- Every observation complex is exact on the zero source and zero admissible sectors. -/
theorem isSourcePointedExactDescent_bot
    {R E F G : Type*} [CommRing R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (observe : E →ₗ[R] F) (compatibility : F →ₗ[R] G) :
    IsSourcePointedExactDescent observe compatibility ⊥ ⊥ := by
  simp [IsSourcePointedExactDescent, IsConservativeOn]

/-- Identity preserves every observer relation in the law-saturation model. -/
theorem preserves_id (S : Set ℕ) : Preserves id S := by
  intro x y hxy
  simpa using hxy

/-- Identity is a compatible unary-law retraction in every unchanged carrier chamber. -/
theorem compatibleUnaryLawRetraction_id
    {α : Type*} (F : Set (α → α)) (E : α → α → Prop) :
    CompatibleUnaryLawRetraction id F F E E id := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro y z h
    exact h
  intro g hg
  exact ⟨g, hg, fun _ => rfl⟩

/-- Marked translation orbit membership is reflexive. -/
theorem markedTranslationSameOrbit_refl
    (p : MultipleGammaPeriodSource →+ ℂ) (x : ℂ) :
    MarkedTranslationSameOrbit p x x := by
  exact ⟨0, by simp⟩

/-- Marked translation orbit membership is symmetric. -/
theorem markedTranslationSameOrbit_symm
    (p : MultipleGammaPeriodSource →+ ℂ) {x y : ℂ}
    (h : MarkedTranslationSameOrbit p x y) :
    MarkedTranslationSameOrbit p y x := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨-n, ?_⟩
  simp

/-- Marked translation orbit membership is transitive. -/
theorem markedTranslationSameOrbit_trans
    (p : MultipleGammaPeriodSource →+ ℂ) {x y z : ℂ}
    (h₁ : MarkedTranslationSameOrbit p x y)
    (h₂ : MarkedTranslationSameOrbit p y z) :
    MarkedTranslationSameOrbit p x z := by
  obtain ⟨n, rfl⟩ := h₁
  obtain ⟨m, rfl⟩ := h₂
  refine ⟨n + m, ?_⟩
  simp [add_assoc]

end GaloisForLFunctions.HTGeometry
