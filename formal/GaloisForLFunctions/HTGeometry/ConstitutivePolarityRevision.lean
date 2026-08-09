import Mathlib.Data.Set.Basic

/-!
# Exact polarity revision collapse

For a fixed compatibility relation between rules and tests, exact reciprocal revision has no open
genesis dynamics.  Serial revision is idempotent, while synchronous revision satisfies `P³ = P`.
Thus every post-first synchronous state is fixed or belongs to a two-cycle.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {X : Type u} {Y : Type v}

/-- Tests passed by every rule in a declared rule family. -/
def constitutiveRulePolar (compatible : X → Y → Prop) (rules : Set X) : Set Y :=
  {y | ∀ x ∈ rules, compatible x y}

/-- Rules passing every test in a declared test family. -/
def constitutiveTestPolar (compatible : X → Y → Prop) (tests : Set Y) : Set X :=
  {x | ∀ y ∈ tests, compatible x y}

theorem constitutiveRulePolar_antitone (compatible : X → Y → Prop)
    {rules₁ rules₂ : Set X} (h : rules₁ ⊆ rules₂) :
    constitutiveRulePolar compatible rules₂ ⊆ constitutiveRulePolar compatible rules₁ := by
  intro y hy x hx
  exact hy x (h hx)

theorem constitutiveTestPolar_antitone (compatible : X → Y → Prop)
    {tests₁ tests₂ : Set Y} (h : tests₁ ⊆ tests₂) :
    constitutiveTestPolar compatible tests₂ ⊆ constitutiveTestPolar compatible tests₁ := by
  intro x hx y hy
  exact hx y (h hy)

/-- Exact rule closure induced by the fixed rule--test polarity. -/
def constitutiveRuleClosure (compatible : X → Y → Prop) (rules : Set X) : Set X :=
  constitutiveTestPolar compatible (constitutiveRulePolar compatible rules)

/-- Exact test closure induced by the fixed rule--test polarity. -/
def constitutiveTestClosure (compatible : X → Y → Prop) (tests : Set Y) : Set Y :=
  constitutiveRulePolar compatible (constitutiveTestPolar compatible tests)

theorem constitutiveRuleClosure_extensive (compatible : X → Y → Prop) (rules : Set X) :
    rules ⊆ constitutiveRuleClosure compatible rules := by
  intro x hx y hy
  exact hy x hx

theorem constitutiveTestClosure_extensive (compatible : X → Y → Prop) (tests : Set Y) :
    tests ⊆ constitutiveTestClosure compatible tests := by
  intro y hy x hx
  exact hx y hy

/-- Triple polarity on rules collapses to one polarity. -/
theorem constitutiveRulePolar_ruleClosure (compatible : X → Y → Prop) (rules : Set X) :
    constitutiveRulePolar compatible (constitutiveRuleClosure compatible rules) =
      constitutiveRulePolar compatible rules := by
  apply Set.Subset.antisymm
  · intro y hy x hx
    exact hy x (constitutiveRuleClosure_extensive compatible rules hx)
  · intro y hy x hx
    exact hx y hy

/-- Triple polarity on tests collapses to one polarity. -/
theorem constitutiveTestPolar_testClosure (compatible : X → Y → Prop) (tests : Set Y) :
    constitutiveTestPolar compatible (constitutiveTestClosure compatible tests) =
      constitutiveTestPolar compatible tests := by
  apply Set.Subset.antisymm
  · intro x hx y hy
    exact hx y (by
      intro z hz
      exact hz y hy)
  · intro x hx y hy
    exact hy x hx

theorem constitutiveRuleClosure_idempotent (compatible : X → Y → Prop) (rules : Set X) :
    constitutiveRuleClosure compatible (constitutiveRuleClosure compatible rules) =
      constitutiveRuleClosure compatible rules := by
  exact congrArg (constitutiveTestPolar compatible)
    (constitutiveRulePolar_ruleClosure compatible rules)

theorem constitutiveTestClosure_idempotent (compatible : X → Y → Prop) (tests : Set Y) :
    constitutiveTestClosure compatible (constitutiveTestClosure compatible tests) =
      constitutiveTestClosure compatible tests := by
  exact congrArg (constitutiveRulePolar compatible)
    (constitutiveTestPolar_testClosure compatible tests)

/-- Exact serial revision: regenerate all tests, then close the rule family against them. -/
def constitutiveSerialRevision (compatible : X → Y → Prop)
    (state : Set X × Set Y) : Set X × Set Y :=
  (constitutiveRuleClosure compatible state.1, constitutiveRulePolar compatible state.1)

/-- Exact synchronous revision: each family is regenerated from the other previous family. -/
def constitutiveParallelRevision (compatible : X → Y → Prop)
    (state : Set X × Set Y) : Set X × Set Y :=
  (constitutiveTestPolar compatible state.2, constitutiveRulePolar compatible state.1)

/-- Serial exact reciprocal revision stabilizes after one full round. -/
theorem constitutiveSerialRevision_idempotent (compatible : X → Y → Prop)
    (state : Set X × Set Y) :
    constitutiveSerialRevision compatible (constitutiveSerialRevision compatible state) =
      constitutiveSerialRevision compatible state := by
  apply Prod.ext
  · exact constitutiveRuleClosure_idempotent compatible state.1
  · exact constitutiveRulePolar_ruleClosure compatible state.1

/-- Two synchronous rounds close the two sides independently. -/
theorem constitutiveParallelRevision_sq (compatible : X → Y → Prop)
    (state : Set X × Set Y) :
    constitutiveParallelRevision compatible (constitutiveParallelRevision compatible state) =
      (constitutiveRuleClosure compatible state.1,
        constitutiveTestClosure compatible state.2) := by
  rfl

/-- Exact synchronous reciprocal revision satisfies the global law `P³ = P`. -/
theorem constitutiveParallelRevision_cube (compatible : X → Y → Prop)
    (state : Set X × Set Y) :
    constitutiveParallelRevision compatible
        (constitutiveParallelRevision compatible
          (constitutiveParallelRevision compatible state)) =
      constitutiveParallelRevision compatible state := by
  apply Prod.ext
  · exact constitutiveTestPolar_testClosure compatible state.2
  · exact constitutiveRulePolar_ruleClosure compatible state.1

/-- Fixed synchronous states are exactly mutually polar rule--test concepts. -/
theorem constitutiveParallelRevision_fixed_iff (compatible : X → Y → Prop)
    (state : Set X × Set Y) :
    constitutiveParallelRevision compatible state = state ↔
      constitutiveTestPolar compatible state.2 = state.1 ∧
        constitutiveRulePolar compatible state.1 = state.2 := by
  constructor
  · intro h
    exact ⟨by simpa [constitutiveParallelRevision] using congrArg Prod.fst h,
      by simpa [constitutiveParallelRevision] using congrArg Prod.snd h⟩
  · rintro ⟨hRules, hTests⟩
    exact Prod.ext hRules hTests

/-- Closed capstone: fixed-polarity revision has only one-round serial closure and post-first
two-periodic synchronous dynamics. -/
theorem constitutiveExactPolarityRevisionMechanism_closed (compatible : X → Y → Prop) :
    (∀ state : Set X × Set Y,
      constitutiveSerialRevision compatible (constitutiveSerialRevision compatible state) =
        constitutiveSerialRevision compatible state) ∧
    (∀ state : Set X × Set Y,
      constitutiveParallelRevision compatible
          (constitutiveParallelRevision compatible state) =
        (constitutiveRuleClosure compatible state.1,
          constitutiveTestClosure compatible state.2)) ∧
    (∀ state : Set X × Set Y,
      constitutiveParallelRevision compatible
          (constitutiveParallelRevision compatible
            (constitutiveParallelRevision compatible state)) =
        constitutiveParallelRevision compatible state) := by
  exact ⟨constitutiveSerialRevision_idempotent compatible,
    constitutiveParallelRevision_sq compatible,
    constitutiveParallelRevision_cube compatible⟩

end GaloisForLFunctions.HTGeometry
