import GaloisForLFunctions.HTGeometry.ConstitutiveFutureReporterPromotion

/-!
# Descent-breaking grammar extension

Adjoining a third legal context operation changes eventual reporter distinctions exactly when that
operation fails to preserve the old future reporter kernel.  Every operation represented by an old
context word preserves the kernel and is therefore prospectively inert.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- Finite words after adjoining one fresh unary context generator. -/
inductive ExtendedLawWord where
  | empty
  | left (tail : ExtendedLawWord)
  | right (tail : ExtendedLawWord)
  | fresh (tail : ExtendedLawWord)
  deriving DecidableEq

namespace ExtendedLawWord

/-- Execute a word in the extended three-generator grammar. -/
def run {α : Type u} (f g h : α → α) : ExtendedLawWord → α → α
  | .empty, x => x
  | .left tail, x => run f g h tail (f x)
  | .right tail, x => run f g h tail (g x)
  | .fresh tail, x => run f g h tail (h x)

/-- Embed every old two-generator context word in the extended grammar. -/
def ofOld : ExchangeLawWord → ExtendedLawWord
  | .empty => .empty
  | .left tail => .left (ofOld tail)
  | .right tail => .right (ofOld tail)

@[simp] theorem run_empty {α : Type u} (f g h : α → α) (x : α) :
    run f g h .empty x = x := rfl

@[simp] theorem run_left {α : Type u} (f g h : α → α)
    (tail : ExtendedLawWord) (x : α) :
    run f g h (.left tail) x = run f g h tail (f x) := rfl

@[simp] theorem run_right {α : Type u} (f g h : α → α)
    (tail : ExtendedLawWord) (x : α) :
    run f g h (.right tail) x = run f g h tail (g x) := rfl

@[simp] theorem run_fresh {α : Type u} (f g h : α → α)
    (tail : ExtendedLawWord) (x : α) :
    run f g h (.fresh tail) x = run f g h tail (h x) := rfl

@[simp] theorem run_ofOld {α : Type u} (f g h : α → α)
    (word : ExchangeLawWord) (x : α) :
    run f g h (ofOld word) x = ExchangeLawWord.run f g word x := by
  induction word generalizing x with
  | empty => rfl
  | left tail ih => exact ih (f x)
  | right tail ih => exact ih (g x)

end ExtendedLawWord

/-- Equality under every future execution after adjoining a fresh generator. -/
def ExtendedFutureReporterKernel {α : Type u} {β : Type v}
    (f g h : α → α) (report : α → β) : α → α → Prop :=
  fun x y => ∀ word,
    report (ExtendedLawWord.run f g h word x) =
      report (ExtendedLawWord.run f g h word y)

theorem extendedFutureReporterKernel_equivalence
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    Equivalence (ExtendedFutureReporterKernel f g h report) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x word
    rfl
  · intro x y hxy word
    exact (hxy word).symm
  · intro x y z hxy hyz word
    exact (hxy word).trans (hyz word)

theorem extendedFutureReporterKernel_preserves_left
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    UnaryPreserves f (ExtendedFutureReporterKernel f g h report) := by
  intro x y hxy word
  exact hxy (.left word)

theorem extendedFutureReporterKernel_preserves_right
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    UnaryPreserves g (ExtendedFutureReporterKernel f g h report) := by
  intro x y hxy word
  exact hxy (.right word)

theorem extendedFutureReporterKernel_preserves_fresh
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    UnaryPreserves h (ExtendedFutureReporterKernel f g h report) := by
  intro x y hxy word
  exact hxy (.fresh word)

/-- Adding a legal operation can only refine the old future-behaviour quotient. -/
theorem extendedFutureReporterKernel_subset_old
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    ∀ ⦃x y⦄, ExtendedFutureReporterKernel f g h report x y →
      FutureReporterKernel f g report x y := by
  intro x y hxy word
  simpa using hxy (ExtendedLawWord.ofOld word)

/-- An extended word preserves the old future kernel whenever the fresh operation does. -/
theorem extendedLawWord_preserves_oldFutureKernel
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β)
    (hh : UnaryPreserves h (FutureReporterKernel f g report))
    (word : ExtendedLawWord) :
    UnaryPreserves (ExtendedLawWord.run f g h word)
      (FutureReporterKernel f g report) := by
  intro x y hxy
  induction word generalizing x y with
  | empty => exact hxy
  | left tail ih =>
      exact ih (futureReporterKernel_preserves_left f g report hxy)
  | right tail ih =>
      exact ih (futureReporterKernel_preserves_right f g report hxy)
  | fresh tail ih => exact ih (hh hxy)

/-- Exact genesis criterion: no prospective refinement occurs exactly when the fresh operation
descends to the old future quotient. -/
theorem fresh_preserves_oldFutureKernel_iff_no_refinement
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    UnaryPreserves h (FutureReporterKernel f g report) ↔
      ∀ x y,
        ExtendedFutureReporterKernel f g h report x y ↔
          FutureReporterKernel f g report x y := by
  constructor
  · intro hh x y
    constructor
    · intro hxy
      exact extendedFutureReporterKernel_subset_old f g h report hxy
    · intro hxy word
      have htransport :=
        extendedLawWord_preserves_oldFutureKernel f g h report hh word hxy
      exact futureReporterKernel_reports_equal f g report htransport
  · intro heq x y hxy word
    have hext : ExtendedFutureReporterKernel f g h report x y := (heq x y).2 hxy
    simpa using hext (.fresh (ExtendedLawWord.ofOld word))

/-- Strict refinement of one binary relation by another. -/
def StrictRelationRefinement {α : Type u}
    (newRelation oldRelation : α → α → Prop) : Prop :=
  (∀ ⦃x y⦄, newRelation x y → oldRelation x y) ∧
    ∃ x y, oldRelation x y ∧ ¬ newRelation x y

/-- Exact strict-birth form of the descent criterion. -/
theorem fresh_not_preserves_iff_strict_refinement
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β) :
    (¬ UnaryPreserves h (FutureReporterKernel f g report)) ↔
      StrictRelationRefinement (ExtendedFutureReporterKernel f g h report)
        (FutureReporterKernel f g report) := by
  classical
  constructor
  · intro hnot
    simp only [UnaryPreserves] at hnot
    push Not at hnot
    rcases hnot with ⟨x, y, hxy, hbreak⟩
    simp only [FutureReporterKernel] at hbreak
    push Not at hbreak
    rcases hbreak with ⟨word, hsep⟩
    refine ⟨extendedFutureReporterKernel_subset_old f g h report, x, y, hxy, ?_⟩
    intro hext
    exact hsep (by simpa using hext (.fresh (ExtendedLawWord.ofOld word)))
  · rintro ⟨_hsubset, x, y, hxy, hnotExtended⟩ hh
    have heq := (fresh_preserves_oldFutureKernel_iff_no_refinement f g h report).1 hh
    exact hnotExtended ((heq x y).2 hxy)

/-- A concrete descent-breaking pair is excluded by the extended future kernel. -/
theorem descentBreaking_witness_not_extended
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β)
    {x y : α} (hxy : FutureReporterKernel f g report x y)
    (word : ExchangeLawWord)
    (hsep : report (ExchangeLawWord.run f g word (h x)) ≠
      report (ExchangeLawWord.run f g word (h y))) :
    FutureReporterKernel f g report x y ∧
      ¬ ExtendedFutureReporterKernel f g h report x y := by
  refine ⟨hxy, ?_⟩
  intro hext
  exact hsep (by simpa using hext (.fresh (ExtendedLawWord.ofOld word)))

namespace ExchangeLawWord

/-- Concatenate old context words, executing the first word before the second. -/
def concat : ExchangeLawWord → ExchangeLawWord → ExchangeLawWord
  | .empty, tail => tail
  | .left head, tail => .left (concat head tail)
  | .right head, tail => .right (concat head tail)

@[simp] theorem run_concat {α : Type u} (f g : α → α)
    (first second : ExchangeLawWord) (x : α) :
    run f g (concat first second) x = run f g second (run f g first x) := by
  induction first generalizing x with
  | empty => rfl
  | left head ih => exact ih (f x)
  | right head ih => exact ih (g x)

/-- Every operation represented by an old word preserves the old future kernel. -/
theorem run_preserves_futureReporterKernel {α : Type u} {β : Type v}
    (f g : α → α) (report : α → β) (oldWord : ExchangeLawWord) :
    UnaryPreserves (run f g oldWord) (FutureReporterKernel f g report) := by
  intro x y hxy continuation
  simpa using hxy (concat oldWord continuation)

end ExchangeLawWord

/-- Definability barrier: a fresh generator equal to an old context word cannot refine eventual
reporter distinctions. -/
theorem oldWordDefinable_fresh_no_refinement
    {α : Type u} {β : Type v} (f g h : α → α) (report : α → β)
    (oldWord : ExchangeLawWord) (hdef : h = ExchangeLawWord.run f g oldWord) :
    ∀ x y,
      ExtendedFutureReporterKernel f g h report x y ↔
        FutureReporterKernel f g report x y := by
  apply (fresh_preserves_oldFutureKernel_iff_no_refinement f g h report).1
  rw [hdef]
  exact ExchangeLawWord.run_preserves_futureReporterKernel f g report oldWord

/-- Three states witnessing source-effective grammar birth erased by a constant observer. -/
inductive GrammarBirthState where
  | a
  | b
  | c
  deriving DecidableEq

def grammarBirthReport : GrammarBirthState → Bool
  | .a => false
  | .b => false
  | .c => true

def grammarBirthFresh : GrammarBirthState → GrammarBirthState
  | .a => .a
  | .b => .c
  | .c => .c

theorem exchangeLawWord_run_id (word : ExchangeLawWord) (x : GrammarBirthState) :
    ExchangeLawWord.run id id word x = x := by
  induction word generalizing x with
  | empty => rfl
  | left tail ih => exact ih x
  | right tail ih => exact ih x

theorem grammarBirth_old_pair_invisible :
    FutureReporterKernel id id grammarBirthReport GrammarBirthState.a GrammarBirthState.b := by
  intro word
  simp [exchangeLawWord_run_id, grammarBirthReport]

theorem grammarBirth_fresh_pair_visible :
    ¬ ExtendedFutureReporterKernel id id grammarBirthFresh grammarBirthReport
      GrammarBirthState.a GrammarBirthState.b := by
  intro hxy
  have hsep := hxy (.fresh .empty)
  simp [grammarBirthFresh, grammarBirthReport] at hsep

theorem grammarBirth_constantObserver_erases_extension :
    ∀ x y,
      ExtendedFutureReporterKernel id id grammarBirthFresh
        (fun _ : GrammarBirthState => PUnit.unit) x y := by
  intro x y word
  rfl

/-- Unconditional capstone: grammar extension is effective exactly by old-quotient escape, old
word definitions are inert, and observation may erase a real source refinement. -/
theorem constitutiveDescentBreakingGrammarExtension_closed :
    (∀ {α : Type u} {β : Type v} (f g h : α → α) (report : α → β),
      UnaryPreserves h (FutureReporterKernel f g report) ↔
        ∀ x y,
          ExtendedFutureReporterKernel f g h report x y ↔
            FutureReporterKernel f g report x y) ∧
    (∀ {α : Type u} {β : Type v} (f g h : α → α) (report : α → β),
      (¬ UnaryPreserves h (FutureReporterKernel f g report)) ↔
        StrictRelationRefinement (ExtendedFutureReporterKernel f g h report)
          (FutureReporterKernel f g report)) ∧
    (∀ {α : Type u} {β : Type v} (f g h : α → α) (report : α → β)
      (oldWord : ExchangeLawWord),
      h = ExchangeLawWord.run f g oldWord →
        ∀ x y,
          ExtendedFutureReporterKernel f g h report x y ↔
            FutureReporterKernel f g report x y) ∧
    FutureReporterKernel id id grammarBirthReport GrammarBirthState.a GrammarBirthState.b ∧
    (¬ ExtendedFutureReporterKernel id id grammarBirthFresh grammarBirthReport
      GrammarBirthState.a GrammarBirthState.b) ∧
    (∀ x y,
      ExtendedFutureReporterKernel id id grammarBirthFresh
        (fun _ : GrammarBirthState => PUnit.unit) x y) := by
  exact ⟨fresh_preserves_oldFutureKernel_iff_no_refinement,
    fresh_not_preserves_iff_strict_refinement,
    fun f g h report oldWord hdef =>
      oldWordDefinable_fresh_no_refinement f g h report oldWord hdef,
    grammarBirth_old_pair_invisible,
    grammarBirth_fresh_pair_visible,
    grammarBirth_constantObserver_erases_extension⟩

end GaloisForLFunctions.HTGeometry
