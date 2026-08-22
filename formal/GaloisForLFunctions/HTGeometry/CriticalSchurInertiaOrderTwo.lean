import GaloisForLFunctions.HTGeometry.CriticalSheetPlaceRamificationIndex
import GaloisForLFunctions.HTGeometry.CriticalSheetUnramifiedOutsideCollision
import GaloisForLFunctions.HTGeometry.CriticalSchurCollisionSupportFibre
import GaloisForLFunctions.HTGeometry.CriticalSchurInertiaOrderBound
import GaloisForLFunctions.HTGeometry.CriticalSchurRamificationIndex

/-!
# The Schur inertia group of the critical horizon has order two

Every collision of the reduced Schur label happens at one point, and the canonical embedding is one
of the colliding sheets — its place is the source Schur place, which ramifies, while an uncollided
sheet is fixed by inertia and so sits over an unramified place.  Hence every sheet either sits over
an unramified place or shares the canonical label, and in the second case cuts out the source Schur
place, whose ramification index is two.  The orbit formula and cyclicity of tame inertia then bound
the inertia group by two, and the ramification of the Schur place bounds it below.

```text
criticalSourceNormalClosureEmbedding_mem_collisionSupport
criticalSheetRamificationIdx_le_two   ** every sheet sits over a place of index at most two **
natCard_criticalSchurInertiaGroup_le_two
natCard_criticalSchurInertiaGroup_eq_two   ** |I| = 2: the Schur fold is simple **
```

This is `(R)` in sharp form.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- **The canonical embedding is a colliding sheet.**  Its place is the source Schur place, which
ramifies, and everything unramified is fixed by inertia. -/
theorem criticalSourceNormalClosureEmbedding_mem_collisionSupport
    (hm : 1 < m) (hn : 1 < n)
    [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)] :
    criticalSourceNormalClosureEmbedding K m n
      ∈ collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn) := by
  classical
  by_contra hσ
  have h1 := criticalSheetRamificationIdx_eq_one_of_notMem_collisionSupport K hm hn hσ
  have h2 := criticalSheetRamificationIdx_eq_two K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn)
    (criticalSheetPullbackValuation_canonical K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
  exact absurd (h1.symm.trans h2) (by norm_num)

/-- **Every sheet of the critical horizon sits over a place of ramification index at most two.**
Outside the collision support the place is unramified; inside it, the sheet shares the reduced label
of the canonical embedding, hence its place, hence its ramification index. -/
theorem criticalSheetRamificationIdx_le_two
    (hm : 1 < m) (hn : 1 < n)
    [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]
    (σ : criticalGeometricSheet K m n) :
    (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
        (criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn))
        (criticalSchurNormalBase_algebraMap_mem K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn))).ramificationIdx
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) ≤ 2 := by
  classical
  by_cases hσ : σ ∈ collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)
  · have hlabel : criticalGeometricSheetToSchurReducedFibre K hm hn σ
        = criticalGeometricSheetToSchurReducedFibre K hm hn
          (criticalSourceNormalClosureEmbedding K m n) :=
      criticalSchur_collisionSupport_reducedFibre_eq K hσ
        (criticalSourceNormalClosureEmbedding_mem_collisionSupport K hm hn)
    exact le_of_eq (criticalSheetRamificationIdx_eq_two K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) (criticalSheetPullbackValuation_eq K hm hn hlabel))
  · exact (criticalSheetRamificationIdx_eq_one_of_notMem_collisionSupport K hm hn hσ).le.trans
      one_le_two

/-- **The Schur inertia group of the critical horizon has order at most two**, unconditionally. -/
theorem natCard_criticalSchurInertiaGroup_le_two (hm : 1 < m) (hn : 1 < n)
    [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)] :
    Nat.card (criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) ≤ 2 := by
  classical
  exact natCard_criticalSchurInertiaGroup_le_two_of_ramification K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn) (criticalSheetRamificationIdx_le_two K hm hn)

/-- **`(R)` in sharp form: the Schur inertia group of the critical horizon has order exactly
two.**  A simple fold. -/
theorem natCard_criticalSchurInertiaGroup_eq_two (hm : 1 < m) (hn : 1 < n)
    [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)] :
    Nat.card (criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) = 2 := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  haveI : Finite (criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn)) := inferInstance
  have hle := natCard_criticalSchurInertiaGroup_le_two K hm hn
  have hge : 1 < Nat.card (criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)) := Finite.one_lt_card
  omega

end

end GaloisForLFunctions.HTGeometry
