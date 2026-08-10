import GaloisForLFunctions.HTGeometry.CriticalSchurReducedSheetInvariance

/-!
# Unique reduced Schur collision forces simple actual inertia

Actual Schur inertia preserves the reduction of every geometric sheet.  If the reduction map has
at most two colliding sheets, the support of each inertia permutation therefore has cardinality at
most two.  Thus every inertia element is trivial or a single transposition.  Nontrivial inertia
then supplies a transposition in the actual critical geometric monodromy group.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

noncomputable local instance criticalGeometricSheetDecidableEqCollision
    (K : Type*) [Field K] (m n : ℕ) :
    DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- If at most two actual sheets collide after reduction at the Schur place, every actual inertia
element acts trivially or by one swap. -/
theorem criticalSchurInertiaAction_eq_one_or_isSwap_of_collisionSupport_ncard_le_two
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hcollision :
      (collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard ≤ 2)
    (g : criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) :
    criticalSchurInertiaAction K (m := m) (n := n)
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g = 1 ∨
      (criticalSchurInertiaAction K (m := m) (n := n)
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g).IsSwap := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  exact permAction_eq_one_or_isSwap_of_collisionSupport_ncard_le_two
    (criticalSchurInertiaAction K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
    (criticalGeometricSheetToSchurReducedFibre K hm hn) hcollision
    (fun g σ =>
      criticalGeometricSheetToSchurReducedFibre_inertia_invariant K hm hn g σ) g

/-- A unique reduced Schur collision together with nontrivial actual inertia produces a literal
transposition in the actual critical geometric monodromy group. -/
theorem exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    [Nontrivial ↥(criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))]
    (hcollision :
      (collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard ≤ 2) :
    ∃ τ : Equiv.Perm (criticalGeometricSheet K m n),
      τ.IsSwap ∧ τ ∈ criticalGeometricMonodromy K m n := by
  exact exists_criticalGeometricMonodromy_isSwap_of_simple_nontrivial_inertia
    K (m := m) (n := n) (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
    (criticalSchurInertiaAction_eq_one_or_isSwap_of_collisionSupport_ncard_le_two
      K hm hn hcollision)

/-- Cardinality two of actual Schur inertia is a premise-free source of the nontriviality instance
needed by the unique-collision transposition criterion. -/
theorem exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two_of_card
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hinertia : Nat.card ↥(criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) = 2)
    (hcollision :
      (collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard ≤ 2) :
    ∃ τ : Equiv.Perm (criticalGeometricSheet K m n),
      τ.IsSwap ∧ τ ∈ criticalGeometricMonodromy K m n := by
  letI : Finite ↥(criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) :=
    Nat.finite_of_card_ne_zero (by omega)
  letI : Nontrivial ↥(criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two
    K hm hn hcollision

end

end GaloisForLFunctions.HTGeometry
