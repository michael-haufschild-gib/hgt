import Mathlib.Tactic

/-!
# Equivariant arity genesis

An unoriented failed pair together with a fixed background cannot generate a deterministic binary
successor while preserving the pair-swap.  Every equivariant separator must carry three distinct
values.  A ternary deterministic reporter is sharp; alternatively, rational convexification adds
the unique fixed mixture `1 / 2`, while an oriented binary reporter resolves the pair by breaking
the swap symmetry.

All headline declarations are closed propositions.  No route-specific or RH premise is used.
-/

namespace GaloisForLFunctions

/-- Minimal failure record: one fixed background and one unoriented Boolean pair. -/
abbrev FailureRecord := Option Bool

/-- Swap the failed pair while fixing the untouched background. -/
def failureRecordSwap : FailureRecord → FailureRecord
  | none => none
  | some b => some (!b)

/-- The deterministic binary target action swaps its two labels. -/
def deterministicBinarySwap (b : Bool) : Bool := !b

/-- Equivariance transports every source fixed point to a target fixed point. -/
theorem fixedPointTransport_closed :
    ∀ (α β : Type) (sα : α → α) (sβ : β → β) (f : α → β) (x : α),
      (∀ a, f (sα a) = sβ (f a)) → sα x = x → sβ (f x) = f x := by
  intro α β sα sβ f x heq hx
  rw [← heq x, hx]

/-- No deterministic binary reporter can preserve the unoriented failure symmetry. -/
theorem no_deterministicBinary_failureReporter_closed :
    ¬ ∃ q : FailureRecord → Bool,
      ∀ x, q (failureRecordSwap x) = deterministicBinarySwap (q x) := by
  rintro ⟨q, hq⟩
  have hfixed := hq none
  simp [failureRecordSwap, deterministicBinarySwap] at hfixed

/-- Every equivariant deterministic reporter resolving the pair has three distinct image values. -/
theorem failureReporter_threeDistinct_closed :
    ∀ (β : Type) (sβ : β → β) (q : FailureRecord → β),
      (∀ x, q (failureRecordSwap x) = sβ (q x)) →
      q (some false) ≠ q (some true) →
      q none ≠ q (some false) ∧
        q none ≠ q (some true) ∧
        q (some false) ≠ q (some true) := by
  intro β sβ q heq hsep
  have hzero := heq none
  have hleft := heq (some false)
  have hright := heq (some true)
  simp only [failureRecordSwap] at hzero hleft hright
  constructor
  · intro h
    apply hsep
    calc
      q (some false) = q none := h.symm
      _ = sβ (q none) := hzero
      _ = sβ (q (some false)) := congrArg sβ h
      _ = q (some true) := hleft.symm
  constructor
  · intro h
    apply hsep
    calc
      q (some false) = sβ (q (some true)) := hright
      _ = sβ (q none) := congrArg sβ h.symm
      _ = q none := hzero.symm
      _ = q (some true) := h
  · exact hsep

/-- The sharp deterministic ternary repair retains the whole failure record. -/
def ternaryFailureReporter : FailureRecord → FailureRecord := id

/-- The ternary reporter preserves the source involution. -/
theorem ternaryFailureReporter_equivariant_closed :
    ∀ x, ternaryFailureReporter (failureRecordSwap x) =
      failureRecordSwap (ternaryFailureReporter x) := by
  intro x
  rfl

/-- The ternary reporter attains the exact three-image lower bound. -/
theorem ternaryFailureReporter_threeDistinct_closed :
    ternaryFailureReporter none ≠ ternaryFailureReporter (some false) ∧
      ternaryFailureReporter none ≠ ternaryFailureReporter (some true) ∧
      ternaryFailureReporter (some false) ≠ ternaryFailureReporter (some true) := by
  simp [ternaryFailureReporter]

/-- Swap the two extreme points of the rational binary probability line. -/
def rationalBinarySwap (p : ℚ) : ℚ := 1 - p

/-- Convex binary repair: the fixed background becomes the symmetric mixture. -/
def rationalConvexFailureReporter : FailureRecord → ℚ
  | none => 1 / 2
  | some false => 0
  | some true => 1

/-- Convexification restores equivariance by supplying a fixed barycenter. -/
theorem rationalConvexFailureReporter_equivariant_closed :
    ∀ x, rationalConvexFailureReporter (failureRecordSwap x) =
      rationalBinarySwap (rationalConvexFailureReporter x) := by
  intro x
  cases x with
  | none => norm_num [failureRecordSwap, rationalConvexFailureReporter, rationalBinarySwap]
  | some b =>
      cases b <;>
        norm_num [failureRecordSwap, rationalConvexFailureReporter, rationalBinarySwap]

/-- The symmetric mixture `1 / 2` is the unique rational fixed point of binary swap. -/
theorem rationalBinarySwap_fixed_iff_half_closed :
    ∀ p : ℚ, rationalBinarySwap p = p ↔ p = 1 / 2 := by
  intro p
  simp only [rationalBinarySwap]
  constructor <;> intro h
  · linarith
  · rw [h]
    norm_num

/-- The convex reporter still resolves the failed pair. -/
theorem rationalConvexFailureReporter_resolves_closed :
    rationalConvexFailureReporter (some false) ≠
      rationalConvexFailureReporter (some true) := by
  norm_num [rationalConvexFailureReporter]

/-- Its background value is genuinely mixed rather than either pure endpoint. -/
theorem rationalConvexFailureReporter_background_mixed_closed :
    rationalConvexFailureReporter none ≠ 0 ∧
      rationalConvexFailureReporter none ≠ 1 := by
  norm_num [rationalConvexFailureReporter]

/-- Choosing an orientation permits a pure binary separator. -/
def orientedBinaryFailureReporter : FailureRecord → Bool
  | none => true
  | some false => false
  | some true => true

/-- The oriented binary reporter separates the failed pair. -/
theorem orientedBinaryFailureReporter_resolves_closed :
    orientedBinaryFailureReporter (some false) ≠
      orientedBinaryFailureReporter (some true) := by
  simp [orientedBinaryFailureReporter]

/-- Binary orientation repairs separation by breaking the original swap equivariance. -/
theorem orientedBinaryFailureReporter_breaks_swap_closed :
    ¬ ∀ x, orientedBinaryFailureReporter (failureRecordSwap x) =
      deterministicBinarySwap (orientedBinaryFailureReporter x) := by
  intro heq
  have hfixed := heq none
  simp [failureRecordSwap, orientedBinaryFailureReporter, deterministicBinarySwap] at hfixed

/-- Closed conjunction of deterministic obstruction, ternary repair, convex repair, and orientation. -/
theorem equivariantArityGenesisMechanism_closed :
    (¬ ∃ q : FailureRecord → Bool,
      ∀ x, q (failureRecordSwap x) = deterministicBinarySwap (q x)) ∧
    (∀ x, ternaryFailureReporter (failureRecordSwap x) =
      failureRecordSwap (ternaryFailureReporter x)) ∧
    (∀ x, rationalConvexFailureReporter (failureRecordSwap x) =
      rationalBinarySwap (rationalConvexFailureReporter x)) ∧
    (∀ p : ℚ, rationalBinarySwap p = p ↔ p = 1 / 2) ∧
    orientedBinaryFailureReporter (some false) ≠
      orientedBinaryFailureReporter (some true) := by
  exact ⟨no_deterministicBinary_failureReporter_closed,
    ternaryFailureReporter_equivariant_closed,
    rationalConvexFailureReporter_equivariant_closed,
    rationalBinarySwap_fixed_iff_half_closed,
    orientedBinaryFailureReporter_resolves_closed⟩

end GaloisForLFunctions
