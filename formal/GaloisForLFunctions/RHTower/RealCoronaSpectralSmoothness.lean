import GaloisForLFunctions.RHTower.RealCoronaLocalDetectabilityFracture

/-!
# All-order smoothness witnesses for partially defined Dirac operators

This module records every iterated commutator as an everywhere-defined bounded extension, while
requiring every extension to preserve the exact domain of the partially defined Dirac operator.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- An all-orders smooth operator for a partially defined Dirac operator.  `derivative (n+1)` is
the bounded extension of `[D, derivative n]` on the exact domain of `D`. -/
structure LinearPMapSmoothElement (D : V →ₗ.[ℂ] V) where
  derivative : ℕ → Module.End ℂ V
  domain_invariant : ∀ n (x : D.domain), derivative n x ∈ D.domain
  commutator_eq : ∀ n (x : D.domain),
    D ⟨derivative n x, domain_invariant n x⟩ - derivative n (D x) =
      derivative (n + 1) x
  bounded : ∀ n, HasLinearOperatorBound (derivative n)

/-- Underlying represented algebra element. -/
def LinearPMapSmoothElement.operator
    {D : V →ₗ.[ℂ] V} (S : LinearPMapSmoothElement D) : Module.End ℂ V :=
  S.derivative 0

theorem LinearPMapSmoothElement.operator_domain_invariant
    {D : V →ₗ.[ℂ] V} (S : LinearPMapSmoothElement D)
    (x : D.domain) : S.operator x ∈ D.domain :=
  S.domain_invariant 0 x

/-- Smoothness supplies the standard bounded first-commutator prerequisite. -/
theorem LinearPMapSmoothElement.firstCommutator_bounded
    {D : V →ₗ.[ℂ] V} (S : LinearPMapSmoothElement D) :
    HasLinearPMapBoundOnDomain
      (linearPMapOrientationCommutator D S.operator
        S.operator_domain_invariant) := by
  rcases S.bounded 1 with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  change ∀ x : D.domain,
    ‖D ⟨S.derivative 0 x, S.domain_invariant 0 x⟩ -
      S.derivative 0 (D x)‖ ≤ C * ‖(x : V)‖
  intro x
  rw [S.commutator_eq 0 x]
  simpa using hbound (x : V)

/-- Transport of the first-order consequence across equality of represented operators. -/
theorem LinearPMapSmoothElement.firstCommutator_bounded_of_operator_eq
    {D : V →ₗ.[ℂ] V} (S : LinearPMapSmoothElement D)
    (a : Module.End ℂ V) (ha : ∀ x : D.domain, a x ∈ D.domain)
    (hSa : S.operator = a) :
    HasLinearPMapBoundOnDomain (linearPMapOrientationCommutator D a ha) := by
  subst a
  simpa only using S.firstCommutator_bounded

/-- Exact commutation with `D` promotes a bounded domain-preserving operator to an all-orders
smooth element: every positive derivative is the zero bounded operator. -/
def linearPMapSmoothElementOfCommutes
    (D : V →ₗ.[ℂ] V) (a : Module.End ℂ V)
    (haDomain : ∀ x : D.domain, a x ∈ D.domain)
    (haCommutes : ∀ x : D.domain, D ⟨a x, haDomain x⟩ = a (D x))
    (haBounded : HasLinearOperatorBound a) :
    LinearPMapSmoothElement D where
  derivative n := if n = 0 then a else 0
  domain_invariant n x := by
    by_cases hn : n = 0
    · simpa [hn] using haDomain x
    · simp [hn]
  commutator_eq n x := by
    cases n with
    | zero =>
        simp only [↓reduceIte, zero_add]
        rw [haCommutes]
        simp
    | succ n =>
        have hsucc : Nat.succ n ≠ 0 := Nat.succ_ne_zero n
        have hnext : Nat.succ n + 1 ≠ 0 := by omega
        simp only [hsucc, ↓reduceIte, hnext, LinearMap.zero_apply, sub_zero]
        exact D.map_zero
  bounded n := by
    by_cases hn : n = 0
    · simpa [hn] using haBounded
    · refine ⟨0, le_rfl, fun x => ?_⟩
      simp [hn]

@[simp] theorem linearPMapSmoothElementOfCommutes_operator
    (D : V →ₗ.[ℂ] V) (a : Module.End ℂ V)
    (haDomain : ∀ x : D.domain, a x ∈ D.domain)
    (haCommutes : ∀ x : D.domain, D ⟨a x, haDomain x⟩ = a (D x))
    (haBounded : HasLinearOperatorBound a) :
    (linearPMapSmoothElementOfCommutes D a haDomain haCommutes haBounded).operator = a := by
  rfl

/-- A genuinely unbounded first commutator excludes every all-orders smooth representative of the
same operator. -/
theorem not_exists_smoothElement_of_genuinelyUnboundedCommutator
    (D : V →ₗ.[ℂ] V) (a : Module.End ℂ V)
    (ha : ∀ x : D.domain, a x ∈ D.domain)
    (hunbounded : IsGenuinelyUnboundedLinearPMap
      (linearPMapOrientationCommutator D a ha)) :
    ¬∃ S : LinearPMapSmoothElement D, S.operator = a := by
  rintro ⟨S, hS⟩
  exact hunbounded (S.firstCommutator_bounded_of_operator_eq a ha hS)

end GaloisForLFunctions.RHTower
