import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionInertia
import GaloisForLFunctions.HTGeometry.CollisionSupportCounting

/-!
# The Schur reduction degree supplies the transposition

The transposition criterion consumes a bound on the *collision support* of the reduction at the
Schur place.  That bound is now a consequence of a pure degree statement: if the reduction loses at
most one sheet, at most two sheets collide.

This is the shape in which the remaining geometric input can be delivered — a count, not a
description of which sheets meet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

noncomputable local instance criticalGeometricSheetDecidableEqDegree
    (K : Type*) [Field K] (m n : ℕ) :
    DecidableEq (criticalGeometricSheet K m n) :=
  Classical.decEq _

/-- **From reduction degree to a monodromy transposition.**  If the Schur reduction of the sheets
loses at most one point, and actual Schur inertia is nontrivial, the actual geometric monodromy
contains a literal transposition. -/
theorem exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    [Nontrivial ↥(criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))]
    [Finite (criticalGeometricSheet K m n)]
    (hdeg : Nat.card (criticalGeometricSheet K m n)
      ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard + 1) :
    ∃ τ : Equiv.Perm (criticalGeometricSheet K m n),
      τ.IsSwap ∧ τ ∈ criticalGeometricMonodromy K m n :=
  exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two K hm hn
    (collisionSupport_ncard_le_two_of_natCard_le_ncard_range _ hdeg)

end

end GaloisForLFunctions.HTGeometry
