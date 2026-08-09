import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Algebra.GroupWithZero.Nat

/-!
# Observer unitization pump

If an observer monoid homomorphism sends a positive-cost source history to the identity, every power
has identical observation, its action grows exactly linearly, its lifted power history is injective,
and its cost cannot descend through the observer.  This is the first exchange theorem of Polarized
Realization Dynamics.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Additive history action grows exactly linearly on powers. -/
theorem constitutiveHistoryAction_pow
    {M : Type*} [Monoid M]
    (A : M → ℕ) (h_one : A 1 = 0)
    (h_mul : ∀ x y : M, A (x * y) = A x + A y)
    (h : M) (n : ℕ) :
    A (h ^ n) = n * A h := by
  induction n with
  | zero => simpa using h_one
  | succ n ih =>
      rw [pow_succ, h_mul, ih, Nat.succ_mul]

/-- An observer that unitizes one history sees every power as the identity. -/
theorem constitutiveObserverUnitization_pow
    {M N : Type*} [Monoid M] [Monoid N]
    (Q : M →* N) {h : M} (hq : Q h = 1) (n : ℕ) :
    Q (h ^ n) = 1 := by
  rw [map_pow, hq, one_pow]

/-- Positive additive action separates all powers of one source history. -/
theorem constitutivePositiveHistory_pow_injective
    {M : Type*} [Monoid M]
    (A : M → ℕ) (h_one : A 1 = 0)
    (h_mul : ∀ x y : M, A (x * y) = A x + A y)
    {h : M} (hpos : 0 < A h) :
    Function.Injective (fun n : ℕ ↦ h ^ n) := by
  intro m n hmn
  have hcost : m * A h = n * A h := by
    exact (constitutiveHistoryAction_pow A h_one h_mul h m).symm.trans
      ((congrArg A hmn).trans (constitutiveHistoryAction_pow A h_one h_mul h n))
  exact Nat.eq_of_mul_eq_mul_right hpos hcost

/-- A positive history cost cannot factor through an observer that sends that history to identity. -/
theorem constitutiveObserverUnitization_cost_not_descend
    {M N : Type*} [Monoid M] [Monoid N]
    (Q : M →* N) (A : M → ℕ)
    {h : M} (hq : Q h = 1) (hpos : 0 < A h) :
    ∀ B : N → ℕ, B 1 = 0 → ¬ (∀ x : M, A x = B (Q x)) := by
  intro B hB hfactor
  have hzero : A h = 0 := by
    rw [hfactor h, hq, hB]
  exact (Nat.ne_of_gt hpos) hzero

/-- One unitized positive history forces recurrent observation, open lifted history, linear action,
and observer nondescendence in one exact package. -/
theorem constitutiveObserverUnitization_pump
    {M N : Type*} [Monoid M] [Monoid N]
    (Q : M →* N)
    (A : M → ℕ) (h_one : A 1 = 0)
    (h_mul : ∀ x y : M, A (x * y) = A x + A y)
    {h : M} (hq : Q h = 1) (hpos : 0 < A h) :
    (∀ n : ℕ, Q (h ^ n) = 1) ∧
      (∀ n : ℕ, A (h ^ n) = n * A h) ∧
      Function.Injective (fun n : ℕ ↦ h ^ n) ∧
      (∀ B : N → ℕ, B 1 = 0 → ¬ (∀ x : M, A x = B (Q x))) := by
  exact ⟨constitutiveObserverUnitization_pow Q hq,
    constitutiveHistoryAction_pow A h_one h_mul h,
    constitutivePositiveHistory_pow_injective A h_one h_mul hpos,
    constitutiveObserverUnitization_cost_not_descend Q A hq hpos⟩

end GaloisForLFunctions.HTGeometry
