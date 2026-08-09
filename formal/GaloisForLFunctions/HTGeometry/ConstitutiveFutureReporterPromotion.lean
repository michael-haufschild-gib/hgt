import GaloisForLFunctions.HTGeometry.ConstitutiveExchangePromotionSelection

/-!
# Future reporter envelopes and strict-promotion corridors

The entire future orbit of a conserved reporter determines the greatest law-invariant relation that
may be quotiented away.  Strict exchange promotion exists exactly when the least relation required
for commutation lies inside this future reporter envelope.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- Finite words in two unary laws. Constructors prefix a new source operation. -/
inductive ExchangeLawWord where
  | empty
  | left (tail : ExchangeLawWord)
  | right (tail : ExchangeLawWord)
  deriving DecidableEq

namespace ExchangeLawWord

/-- Execute a finite two-law word. -/
def run {α : Type u} (f g : α → α) : ExchangeLawWord → α → α
  | empty, x => x
  | left tail, x => run f g tail (f x)
  | right tail, x => run f g tail (g x)

@[simp] theorem run_empty {α : Type u} (f g : α → α) (x : α) :
    run f g empty x = x := rfl

@[simp] theorem run_left {α : Type u} (f g : α → α) (tail : ExchangeLawWord) (x : α) :
    run f g (left tail) x = run f g tail (f x) := rfl

@[simp] theorem run_right {α : Type u} (f g : α → α) (tail : ExchangeLawWord) (x : α) :
    run f g (right tail) x = run f g tail (g x) := rfl

end ExchangeLawWord

/-- Equality under every future execution of the two laws followed by the reporter. -/
def FutureReporterKernel {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) : α → α → Prop :=
  fun x y => ∀ w, r (ExchangeLawWord.run f g w x) = r (ExchangeLawWord.run f g w y)

theorem futureReporterKernel_equivalence {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) : Equivalence (FutureReporterKernel f g r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x w
    rfl
  · intro x y hxy w
    exact (hxy w).symm
  · intro x y z hxy hyz w
    exact (hxy w).trans (hyz w)

theorem futureReporterKernel_preserves_left {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) : UnaryPreserves f (FutureReporterKernel f g r) := by
  intro x y hxy w
  exact hxy (.left w)

theorem futureReporterKernel_preserves_right {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) : UnaryPreserves g (FutureReporterKernel f g r) := by
  intro x y hxy w
  exact hxy (.right w)

theorem futureReporterKernel_reports_equal {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) {x y : α}
    (hxy : FutureReporterKernel f g r x y) : r x = r y := by
  exact hxy .empty

/-- The future reporter kernel is the greatest preserved equivalence inside the reporter kernel. -/
theorem futureReporterKernel_greatest {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) {E : α → α → Prop}
    (_hE : Equivalence E) (hf : UnaryPreserves f E) (hg : UnaryPreserves g E)
    (hr : ∀ ⦃x y⦄, E x y → r x = r y) :
    ∀ ⦃x y⦄, E x y → FutureReporterKernel f g r x y := by
  intro x y hxy w
  induction w generalizing x y with
  | empty => exact hr hxy
  | left tail ih => exact ih (hf hxy)
  | right tail ih => exact ih (hg hxy)

/-- Exact criterion: the minimal exchange relation fits the future reporter envelope precisely when
every generating exchange pair remains invisible in every future context. -/
theorem exchangeCongruence_subset_futureReporterKernel_iff
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β) :
    (∀ ⦃x y⦄, ExchangeCongruence f g x y → FutureReporterKernel f g r x y) ↔
      ∀ x w,
        r (ExchangeLawWord.run f g w (f (g x))) =
          r (ExchangeLawWord.run f g w (g (f x))) := by
  constructor
  · intro h x w
    exact h (exchangeCongruence_contains f g x) w
  · intro h
    apply exchangeCongruence_least (futureReporterKernel_equivalence f g r)
    · exact futureReporterKernel_preserves_left f g r
    · exact futureReporterKernel_preserves_right f g r
    · intro x w
      exact h x w

/-- A strict promotion which executes both laws, makes their exchange pairs equal, and conserves
the declared reporter. -/
def ReporterStrictExchangePromotion {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) (E : α → α → Prop) : Prop :=
  Equivalence E ∧
    UnaryPreserves f E ∧
    UnaryPreserves g E ∧
    (∀ x, E (f (g x)) (g (f x))) ∧
    (∀ ⦃x y⦄, E x y → r x = r y)

def ReporterStrictExchangePromotionExists {α : Type u} {β : Type v}
    (f g : α → α) (r : α → β) : Prop :=
  ∃ E, ReporterStrictExchangePromotion f g r E

/-- Every legal reporter-conserving strict promotion lies between the least required exchange
congruence and the greatest future-reporter-permitted congruence. -/
theorem reporterStrictExchangePromotion_corridor
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β)
    {E : α → α → Prop} (hprom : ReporterStrictExchangePromotion f g r E) :
    (∀ ⦃x y⦄, ExchangeCongruence f g x y → E x y) ∧
      (∀ ⦃x y⦄, E x y → FutureReporterKernel f g r x y) := by
  rcases hprom with ⟨hE, hf, hg, hexchange, hr⟩
  exact ⟨exchangeCongruence_least hE hf hg hexchange,
    futureReporterKernel_greatest f g r hE hf hg hr⟩

theorem reporterStrictExchangePromotionExists_iff
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β) :
    ReporterStrictExchangePromotionExists f g r ↔
      ∀ ⦃x y⦄, ExchangeCongruence f g x y → FutureReporterKernel f g r x y := by
  constructor
  · rintro ⟨E, hprom⟩ x y hxy
    have corridor := reporterStrictExchangePromotion_corridor f g r hprom
    exact corridor.2 (corridor.1 hxy)
  · intro hfit
    refine ⟨ExchangeCongruence f g, exchangeCongruence_equivalence f g,
      exchangeCongruence_preserves_left f g, exchangeCongruence_preserves_right f g,
      exchangeCongruence_contains f g, ?_⟩
    intro x y hxy
    exact futureReporterKernel_reports_equal f g r (hfit hxy)

theorem reporterStrictExchangePromotionExists_iff_futureCriticalPairs
    {α : Type u} {β : Type v} (f g : α → α) (r : α → β) :
    ReporterStrictExchangePromotionExists f g r ↔
      ∀ x w,
        r (ExchangeLawWord.run f g w (f (g x))) =
          r (ExchangeLawWord.run f g w (g (f x))) := by
  rw [reporterStrictExchangePromotionExists_iff]
  exact exchangeCongruence_subset_futureReporterKernel_iff f g r

/-- Five states witnessing delayed detection of a presently invisible exchange residual. -/
inductive DelayedExchangeState where
  | seed
  | leftInput
  | rightInput
  | leftResult
  | rightResult
  deriving DecidableEq

def delayedExchangeLeft : DelayedExchangeState → DelayedExchangeState
  | .seed => .rightInput
  | .leftInput => .leftResult
  | .rightInput => .rightInput
  | .leftResult => .seed
  | .rightResult => .rightResult

def delayedExchangeRight : DelayedExchangeState → DelayedExchangeState
  | .seed => .leftInput
  | .leftInput => .leftInput
  | .rightInput => .rightResult
  | .leftResult => .leftResult
  | .rightResult => .rightResult

def delayedExchangeReporter : DelayedExchangeState → Bool
  | .seed => true
  | _ => false

theorem delayedExchange_rawReporter_blind :
    delayedExchangeReporter
        (delayedExchangeLeft (delayedExchangeRight .seed)) =
      delayedExchangeReporter
        (delayedExchangeRight (delayedExchangeLeft .seed)) := by
  rfl

theorem delayedExchange_futureReporter_detects :
    delayedExchangeReporter
        (ExchangeLawWord.run delayedExchangeLeft delayedExchangeRight (.left .empty)
          (delayedExchangeLeft (delayedExchangeRight .seed))) ≠
      delayedExchangeReporter
        (ExchangeLawWord.run delayedExchangeLeft delayedExchangeRight (.left .empty)
          (delayedExchangeRight (delayedExchangeLeft .seed))) := by
  intro h
  cases h

theorem delayedExchange_no_reporterConserving_strictPromotion :
    ¬ ReporterStrictExchangePromotionExists
      delayedExchangeLeft delayedExchangeRight delayedExchangeReporter := by
  intro hexists
  have hfit :=
    (reporterStrictExchangePromotionExists_iff
      delayedExchangeLeft delayedExchangeRight delayedExchangeReporter).1 hexists
  have hfuture := hfit
    (exchangeCongruence_contains delayedExchangeLeft delayedExchangeRight .seed)
  exact delayedExchange_futureReporter_detects (hfuture (.left .empty))

theorem constitutiveFutureReporterPromotionMechanism_closed
    {α : Type u} {β : Type v} :
    (∀ (f g : α → α) (r : α → β), Equivalence (FutureReporterKernel f g r)) ∧
    (∀ (f g : α → α) (r : α → β),
      ReporterStrictExchangePromotionExists f g r ↔
        ∀ x w,
          r (ExchangeLawWord.run f g w (f (g x))) =
            r (ExchangeLawWord.run f g w (g (f x)))) ∧
    (delayedExchangeReporter
        (delayedExchangeLeft (delayedExchangeRight .seed)) =
      delayedExchangeReporter
        (delayedExchangeRight (delayedExchangeLeft .seed))) ∧
    ¬ ReporterStrictExchangePromotionExists
      delayedExchangeLeft delayedExchangeRight delayedExchangeReporter := by
  exact ⟨futureReporterKernel_equivalence,
    reporterStrictExchangePromotionExists_iff_futureCriticalPairs,
    delayedExchange_rawReporter_blind,
    delayedExchange_no_reporterConserving_strictPromotion⟩

end GaloisForLFunctions.HTGeometry
