import GaloisForLFunctions.HTGeometry.ConstitutiveContextualChallengeTransduction
import GaloisForLFunctions.HTGeometry.ConstitutiveFutureReporterPromotion

/-!
# Prospective challenge geometry

Finite future contexts define nested equivalence relations.  Their intersection is the full future
reporter kernel, a single exact plateau is permanent, and postobservation can only delay or erase
pairwise separation.  Finite Boolean lists supply a coherent finite-horizon signature with no
global source realization.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

namespace ExchangeLawWord

/-- Number of legal context generators in a future word. -/
def depth : ExchangeLawWord → ℕ
  | .empty => 0
  | .left tail => depth tail + 1
  | .right tail => depth tail + 1

@[simp] theorem depth_empty : depth .empty = 0 := rfl

@[simp] theorem depth_left (tail : ExchangeLawWord) :
    depth (.left tail) = depth tail + 1 := rfl

@[simp] theorem depth_right (tail : ExchangeLawWord) :
    depth (.right tail) = depth tail + 1 := rfl

theorem depth_eq_zero_iff (word : ExchangeLawWord) :
    depth word = 0 ↔ word = .empty := by
  cases word <;> simp

end ExchangeLawWord

/-- Agreement under every legal future context of depth strictly below `n`. -/
def ProspectiveAgreement {α : Type u} {β : Type v}
    (f g : α → α) (report : α → β) (n : ℕ) : α → α → Prop :=
  fun x y => ∀ word, ExchangeLawWord.depth word < n →
    report (ExchangeLawWord.run f g word x) =
      report (ExchangeLawWord.run f g word y)

theorem prospectiveAgreement_equivalence {α : Type u} {β : Type v}
    (f g : α → α) (report : α → β) (n : ℕ) :
    Equivalence (ProspectiveAgreement f g report n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x word _hdepth
    rfl
  · intro x y hxy word hdepth
    exact (hxy word hdepth).symm
  · intro x y z hxy hyz word hdepth
    exact (hxy word hdepth).trans (hyz word hdepth)

/-- Longer prospective horizons refine shorter ones. -/
theorem prospectiveAgreement_mono {α : Type u} {β : Type v}
    {f g : α → α} {report : α → β} {m n : ℕ} (hmn : m ≤ n) {x y : α}
    (hxy : ProspectiveAgreement f g report n x y) :
    ProspectiveAgreement f g report m x y := by
  intro word hdepth
  exact hxy word (Nat.lt_of_lt_of_le hdepth hmn)

/-- Prefixing the left context generator shifts the agreement horizon down by one. -/
theorem prospectiveAgreement_left_shift {α : Type u} {β : Type v}
    (f g : α → α) (report : α → β) (n : ℕ) {x y : α}
    (hxy : ProspectiveAgreement f g report (n + 1) x y) :
    ProspectiveAgreement f g report n (f x) (f y) := by
  intro word hdepth
  exact hxy (.left word) (by simp only [ExchangeLawWord.depth_left]; omega)

/-- Prefixing the right context generator shifts the agreement horizon down by one. -/
theorem prospectiveAgreement_right_shift {α : Type u} {β : Type v}
    (f g : α → α) (report : α → β) (n : ℕ) {x y : α}
    (hxy : ProspectiveAgreement f g report (n + 1) x y) :
    ProspectiveAgreement f g report n (g x) (g y) := by
  intro word hdepth
  exact hxy (.right word) (by simp only [ExchangeLawWord.depth_right]; omega)

/-- The full future reporter kernel is exactly agreement at every finite horizon. -/
theorem futureReporterKernel_iff_forall_prospectiveAgreement
    {α : Type u} {β : Type v} (f g : α → α) (report : α → β) (x y : α) :
    FutureReporterKernel f g report x y ↔
      ∀ n, ProspectiveAgreement f g report n x y := by
  constructor
  · intro hfuture n word _hdepth
    exact hfuture word
  · intro hall word
    exact hall (ExchangeLawWord.depth word + 1) word (by omega)

/-- A single exact plateau is already the full future reporter kernel. -/
theorem prospectiveAgreement_plateau_iff_futureReporterKernel
    {α : Type u} {β : Type v} (f g : α → α) (report : α → β) (n : ℕ)
    (hplateau : ∀ x y,
      ProspectiveAgreement f g report n x y ↔
        ProspectiveAgreement f g report (n + 1) x y)
    (x y : α) :
    ProspectiveAgreement f g report n x y ↔
      FutureReporterKernel f g report x y := by
  have hleft : UnaryPreserves f (ProspectiveAgreement f g report n) := by
    intro a b hab
    exact prospectiveAgreement_left_shift f g report n ((hplateau a b).1 hab)
  have hright : UnaryPreserves g (ProspectiveAgreement f g report n) := by
    intro a b hab
    exact prospectiveAgreement_right_shift f g report n ((hplateau a b).1 hab)
  have hre : ∀ ⦃a b⦄, ProspectiveAgreement f g report n a b → report a = report b := by
    intro a b hab
    have hnext := (hplateau a b).1 hab
    exact hnext .empty (by simp)
  constructor
  · intro hxy
    exact futureReporterKernel_greatest f g report
      (prospectiveAgreement_equivalence f g report n) hleft hright hre hxy
  · intro hfuture
    exact (futureReporterKernel_iff_forall_prospectiveAgreement f g report x y).1 hfuture n

/-- After one exact plateau, every later horizon is permanently equal to it. -/
theorem prospectiveAgreement_plateau_permanent
    {α : Type u} {β : Type v} (f g : α → α) (report : α → β) (n : ℕ)
    (hplateau : ∀ x y,
      ProspectiveAgreement f g report n x y ↔
        ProspectiveAgreement f g report (n + 1) x y) :
    ∀ m, n ≤ m → ∀ x y,
      ProspectiveAgreement f g report m x y ↔
        ProspectiveAgreement f g report n x y := by
  intro m hnm x y
  constructor
  · exact prospectiveAgreement_mono hnm
  · intro hn
    have hfuture :=
      (prospectiveAgreement_plateau_iff_futureReporterKernel f g report n hplateau x y).1 hn
    exact (futureReporterKernel_iff_forall_prospectiveAgreement f g report x y).1 hfuture m

/-- Postobservation can only coarsen every prospective horizon. -/
theorem prospectiveAgreement_postobserve {α : Type u} {β : Type v} {γ : Type w}
    (f g : α → α) (report : α → β) (post : β → γ) (n : ℕ) {x y : α}
    (hxy : ProspectiveAgreement f g report n x y) :
    ProspectiveAgreement f g (post ∘ report) n x y := by
  intro word hdepth
  exact congrArg post (hxy word hdepth)

/-- An injective postobserver preserves every prospective horizon exactly. -/
theorem prospectiveAgreement_postobserve_iff_of_injective
    {α : Type u} {β : Type v} {γ : Type w}
    (f g : α → α) (report : α → β) (post : β → γ)
    (hpost : Function.Injective post) (n : ℕ) (x y : α) :
    ProspectiveAgreement f g (post ∘ report) n x y ↔
      ProspectiveAgreement f g report n x y := by
  constructor
  · intro hxy word hdepth
    exact hpost (hxy word hdepth)
  · exact prospectiveAgreement_postobserve f g report post n

/-- Three states witnessing delayed observer exposure of an earlier source distinction. -/
inductive ProspectiveDelayState where
  | a
  | b
  | c
  deriving DecidableEq

def prospectiveDelayLeft : ProspectiveDelayState → ProspectiveDelayState
  | .a => .a
  | .b => .c
  | .c => .c

def prospectiveDelayRight : ProspectiveDelayState → ProspectiveDelayState := id

def prospectiveDelayObserver : ProspectiveDelayState → Bool
  | .a => false
  | .b => false
  | .c => true

theorem prospectiveDelay_source_separated_at_horizon_one :
    ¬ ProspectiveAgreement prospectiveDelayLeft prospectiveDelayRight id 1
      .a .b := by
  intro h
  have hab := h .empty (by simp)
  simp at hab

theorem prospectiveDelay_observer_agrees_at_horizon_one :
    ProspectiveAgreement prospectiveDelayLeft prospectiveDelayRight
      prospectiveDelayObserver 1 .a .b := by
  intro word hdepth
  have hzero : ExchangeLawWord.depth word = 0 := Nat.lt_one_iff.mp hdepth
  have hempty : word = .empty :=
    (ExchangeLawWord.depth_eq_zero_iff word).mp hzero
  subst word
  rfl

theorem prospectiveDelay_observer_separated_at_horizon_two :
    ¬ ProspectiveAgreement prospectiveDelayLeft prospectiveDelayRight
      prospectiveDelayObserver 2 .a .b := by
  intro h
  have hab := h (.left .empty) (by simp [ExchangeLawWord.depth])
  simp [prospectiveDelayLeft, prospectiveDelayObserver] at hab

/-- Future Boolean report of a finite list, with `false` after its end. -/
def finiteBooleanSignature : List Bool → ℕ → Bool
  | [], _ => false
  | head :: _tail, 0 => head
  | _head :: tail, n + 1 => finiteBooleanSignature tail n

/-- Every finite prefix of the all-true coherent history is source-realized. -/
theorem finiteBooleanSignature_replicate_true
    (n k : ℕ) (hk : k < n) :
    finiteBooleanSignature (List.replicate n true) k = true := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
      cases k with
      | zero =>
          change finiteBooleanSignature (true :: List.replicate n true) 0 = true
          rfl
      | succ k =>
          simp only [List.replicate_succ, finiteBooleanSignature]
          exact ih k (by omega)

theorem finiteBooleanSignature_every_horizon_realized (n : ℕ) :
    ∃ state : List Bool, ∀ k, k < n → finiteBooleanSignature state k = true := by
  exact ⟨List.replicate n true, finiteBooleanSignature_replicate_true n⟩

/-- No finite Boolean list realizes the all-true coherent history globally. -/
theorem finiteBooleanSignature_not_globally_all_true (state : List Bool) :
    ¬ ∀ k, finiteBooleanSignature state k = true := by
  induction state with
  | nil =>
      intro hall
      simpa [finiteBooleanSignature] using hall 0
  | cons head tail ih =>
      intro hall
      apply ih
      intro k
      simpa [finiteBooleanSignature] using hall (k + 1)

theorem finiteBooleanSignature_all_true_not_source_realized :
    ¬ ∃ state : List Bool, ∀ k, finiteBooleanSignature state k = true := by
  rintro ⟨state, hall⟩
  exact finiteBooleanSignature_not_globally_all_true state hall

/-- Unconditional capstone: fixed-grammar prospective geometry has permanent plateaux, observer
delay is real, and finite-horizon realization does not force one global source state. -/
theorem constitutiveProspectiveChallengeGeometry_closed :
    (∀ {α : Type u} {β : Type v} (f g : α → α) (report : α → β) (n : ℕ),
      (∀ x y,
        ProspectiveAgreement f g report n x y ↔
          ProspectiveAgreement f g report (n + 1) x y) →
      ∀ m, n ≤ m → ∀ x y,
        ProspectiveAgreement f g report m x y ↔
          ProspectiveAgreement f g report n x y) ∧
    (¬ ProspectiveAgreement prospectiveDelayLeft prospectiveDelayRight id 1
      ProspectiveDelayState.a ProspectiveDelayState.b) ∧
    ProspectiveAgreement prospectiveDelayLeft prospectiveDelayRight
      prospectiveDelayObserver 1 ProspectiveDelayState.a ProspectiveDelayState.b ∧
    (¬ ProspectiveAgreement prospectiveDelayLeft prospectiveDelayRight
      prospectiveDelayObserver 2 ProspectiveDelayState.a ProspectiveDelayState.b) ∧
    (∀ n, ∃ state : List Bool, ∀ k, k < n →
      finiteBooleanSignature state k = true) ∧
    (¬ ∃ state : List Bool, ∀ k, finiteBooleanSignature state k = true) := by
  exact ⟨prospectiveAgreement_plateau_permanent,
    prospectiveDelay_source_separated_at_horizon_one,
    prospectiveDelay_observer_agrees_at_horizon_one,
    prospectiveDelay_observer_separated_at_horizon_two,
    finiteBooleanSignature_every_horizon_realized,
    finiteBooleanSignature_all_true_not_source_realized⟩

end GaloisForLFunctions.HTGeometry
