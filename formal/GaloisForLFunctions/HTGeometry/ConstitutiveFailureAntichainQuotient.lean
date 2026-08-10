import GaloisForLFunctions.HTGeometry.ConstitutivePrimitiveSpectrumTransport

/-!
# Failure-antichain semantic quotient

Mutual inclusion-domination of finite failure families preserves local admission, executable
admission, dominated splitting, primitivity, exact symbolic-execution gaps, and every occurring
primitive degree.  In particular, inserting a failure kernel containing an already present kernel
is a semantically redundant presentation move.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

universe u

/-- `H` dominates `G` when every kernel tested by `G` contains a kernel already tested by `H`. -/
def FailureFamilyDominates {α : Type u} [DecidableEq α]
    (H G : Finset (Finset α)) : Prop :=
  ∀ L ∈ G, ∃ K ∈ H, K ⊆ L

/-- Two failure presentations have the same antichain semantics when they mutually dominate. -/
def FailureFamilySemanticallyEquivalent {α : Type u} [DecidableEq α]
    (H G : Finset (Finset α)) : Prop :=
  FailureFamilyDominates H G ∧ FailureFamilyDominates G H

/-- Failure-family domination is reflexive. -/
theorem failureFamilyDominates_refl {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) :
    FailureFamilyDominates H H := by
  intro K hK
  exact ⟨K, hK, fun _ hi => hi⟩

/-- Failure-family domination is transitive. -/
theorem failureFamilyDominates_trans {α : Type u} [DecidableEq α]
    {H G F : Finset (Finset α)}
    (hHG : FailureFamilyDominates H G)
    (hGF : FailureFamilyDominates G F) :
    FailureFamilyDominates H F := by
  intro L hLF
  obtain ⟨K, hKG, hKL⟩ := hGF L hLF
  obtain ⟨J, hJH, hJK⟩ := hHG K hKG
  exact ⟨J, hJH, hJK.trans hKL⟩

/-- Mutual domination is reflexive. -/
theorem failureFamilySemanticallyEquivalent_refl {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) :
    FailureFamilySemanticallyEquivalent H H :=
  ⟨failureFamilyDominates_refl H, failureFamilyDominates_refl H⟩

/-- Mutual domination is symmetric. -/
theorem failureFamilySemanticallyEquivalent_symm {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (h : FailureFamilySemanticallyEquivalent H G) :
    FailureFamilySemanticallyEquivalent G H :=
  ⟨h.2, h.1⟩

/-- Mutual domination is transitive and therefore defines a semantic equivalence relation. -/
theorem failureFamilySemanticallyEquivalent_trans {α : Type u} [DecidableEq α]
    {H G F : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (hGF : FailureFamilySemanticallyEquivalent G F) :
    FailureFamilySemanticallyEquivalent H F :=
  ⟨failureFamilyDominates_trans hHG.1 hGF.1,
    failureFamilyDominates_trans hGF.2 hHG.2⟩

/-- A dominating failure family implies every local inequality of the dominated family. -/
theorem weightedLocalRepair_of_failureFamilyDominates {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilyDominates H G)
    (m : ℕ) (a : α → ℕ)
    (hlocal : WeightedLocalRepair H m a) :
    WeightedLocalRepair G m a := by
  intro L hLG
  obtain ⟨K, hKH, hKL⟩ := hHG L hLG
  exact (hlocal K hKH).trans (Finset.sum_le_sum_of_subset hKL)

/-- Local admission depends only on the mutual-domination class of the failure presentation. -/
theorem weightedLocalRepair_semantic_iff {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (m : ℕ) (a : α → ℕ) :
    WeightedLocalRepair H m a ↔ WeightedLocalRepair G m a := by
  exact ⟨weightedLocalRepair_of_failureFamilyDominates hHG.1 m a,
    weightedLocalRepair_of_failureFamilyDominates hHG.2 m a⟩

/-- Executable admission depends only on failure-antichain semantics. -/
theorem weightedExecutableRepair_semantic_iff {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (m : ℕ) (a : α → ℕ) :
    WeightedExecutableRepair H m a ↔ WeightedExecutableRepair G m a := by
  constructor
  · rintro ⟨pieces, hpieces, hdom⟩
    exact ⟨pieces, fun j => (weightedLocalRepair_semantic_iff hHG 1 (pieces j)).mp (hpieces j),
      hdom⟩
  · rintro ⟨pieces, hpieces, hdom⟩
    exact ⟨pieces, fun j => (weightedLocalRepair_semantic_iff hHG 1 (pieces j)).mpr (hpieces j),
      hdom⟩

/-- Dominated positive splitting depends only on failure-antichain semantics. -/
theorem weightedDominatedSplit_semantic_iff {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (m : ℕ) (a : α → ℕ) :
    WeightedDominatedSplit H m a ↔ WeightedDominatedSplit G m a := by
  constructor
  · rintro ⟨m₁, m₂, a₁, a₂, hm₁, hm₂, hgrade, hlocal₁, hlocal₂, hdom⟩
    exact ⟨m₁, m₂, a₁, a₂, hm₁, hm₂, hgrade,
      (weightedLocalRepair_semantic_iff hHG m₁ a₁).mp hlocal₁,
      (weightedLocalRepair_semantic_iff hHG m₂ a₂).mp hlocal₂, hdom⟩
  · rintro ⟨m₁, m₂, a₁, a₂, hm₁, hm₂, hgrade, hlocal₁, hlocal₂, hdom⟩
    exact ⟨m₁, m₂, a₁, a₂, hm₁, hm₂, hgrade,
      (weightedLocalRepair_semantic_iff hHG m₁ a₁).mpr hlocal₁,
      (weightedLocalRepair_semantic_iff hHG m₂ a₂).mpr hlocal₂, hdom⟩

/-- Primitive laws depend only on failure-antichain semantics. -/
theorem weightedPrimitiveRepair_semantic_iff {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (m : ℕ) (a : α → ℕ) :
    WeightedPrimitiveRepair H m a ↔ WeightedPrimitiveRepair G m a := by
  constructor
  · rintro ⟨hm, hlocal, hnosplit⟩
    exact ⟨hm, (weightedLocalRepair_semantic_iff hHG m a).mp hlocal,
      fun hsplit => hnosplit ((weightedDominatedSplit_semantic_iff hHG m a).mpr hsplit)⟩
  · rintro ⟨hm, hlocal, hnosplit⟩
    exact ⟨hm, (weightedLocalRepair_semantic_iff hHG m a).mpr hlocal,
      fun hsplit => hnosplit ((weightedDominatedSplit_semantic_iff hHG m a).mp hsplit)⟩

/-- Exact symbolic admission without executable admission. -/
def WeightedSymbolicExecutionGap {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) (m : ℕ) (a : α → ℕ) : Prop :=
  WeightedLocalRepair H m a ∧ ¬ WeightedExecutableRepair H m a

/-- The exact symbolic-execution gap depends only on failure-antichain semantics. -/
theorem weightedSymbolicExecutionGap_semantic_iff {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (m : ℕ) (a : α → ℕ) :
    WeightedSymbolicExecutionGap H m a ↔ WeightedSymbolicExecutionGap G m a := by
  constructor
  · rintro ⟨hlocal, hnotexec⟩
    exact ⟨(weightedLocalRepair_semantic_iff hHG m a).mp hlocal,
      fun hexec => hnotexec ((weightedExecutableRepair_semantic_iff hHG m a).mpr hexec)⟩
  · rintro ⟨hlocal, hnotexec⟩
    exact ⟨(weightedLocalRepair_semantic_iff hHG m a).mpr hlocal,
      fun hexec => hnotexec ((weightedExecutableRepair_semantic_iff hHG m a).mp hexec)⟩

/-- Every occurring primitive degree is an invariant of failure-antichain semantics. -/
theorem primitiveDegreeOccurs_semantic_iff {α : Type u} [DecidableEq α]
    {H G : Finset (Finset α)}
    (hHG : FailureFamilySemanticallyEquivalent H G)
    (m : ℕ) :
    PrimitiveDegreeOccurs H m ↔ PrimitiveDegreeOccurs G m := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (weightedPrimitiveRepair_semantic_iff hHG m a).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (weightedPrimitiveRepair_semantic_iff hHG m a).mpr ha⟩

/-- Inserting a kernel containing an already present kernel is a semantically redundant move. -/
theorem failureFamilySemanticallyEquivalent_insert_dominated
    {α : Type u} [DecidableEq α]
    (H : Finset (Finset α)) {K₀ L : Finset α}
    (hK₀ : K₀ ∈ H) (hsub : K₀ ⊆ L) :
    FailureFamilySemanticallyEquivalent H (insert L H) := by
  constructor
  · intro K hK
    rcases Finset.mem_insert.mp hK with hKL | hKH
    · subst K
      exact ⟨K₀, hK₀, hsub⟩
    · exact ⟨K, hKH, fun _ hi => hi⟩
  · intro K hKH
    exact ⟨K, Finset.mem_insert_of_mem hKH, fun _ hi => hi⟩

/-- Closed capstone: mutual domination is the semantic quotient for all principal SELM predicates,
and dominated-superset insertion is an unconditional stable presentation move. -/
theorem failureAntichainSemanticQuotientMechanism_closed :
    (∀ (α : Type) (_ : DecidableEq α) (H G : Finset (Finset α)),
      FailureFamilySemanticallyEquivalent H G →
      ∀ m a,
        (WeightedLocalRepair H m a ↔ WeightedLocalRepair G m a) ∧
        (WeightedExecutableRepair H m a ↔ WeightedExecutableRepair G m a) ∧
        (WeightedPrimitiveRepair H m a ↔ WeightedPrimitiveRepair G m a) ∧
        (WeightedSymbolicExecutionGap H m a ↔ WeightedSymbolicExecutionGap G m a)) ∧
    (∀ (α : Type) (_ : DecidableEq α) (H : Finset (Finset α)) (K₀ L : Finset α),
      K₀ ∈ H → K₀ ⊆ L →
        FailureFamilySemanticallyEquivalent H (insert L H)) := by
  constructor
  · intro α inst H G hHG m a
    letI : DecidableEq α := inst
    exact ⟨weightedLocalRepair_semantic_iff hHG m a,
      weightedExecutableRepair_semantic_iff hHG m a,
      weightedPrimitiveRepair_semantic_iff hHG m a,
      weightedSymbolicExecutionGap_semantic_iff hHG m a⟩
  · intro α inst H K₀ L hK₀ hsub
    letI : DecidableEq α := inst
    exact failureFamilySemanticallyEquivalent_insert_dominated H hK₀ hsub

end GaloisForLFunctions.HTGeometry
