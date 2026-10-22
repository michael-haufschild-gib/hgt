import GaloisForLFunctions.HTGeometry.Critical.Sheet.OrbitRamification
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.ReducedSheetInvariance
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyJordan

/-!
# Ramification of the horizon is concentrated on the collision support

Inertia preserves the reduced fibre label, so its support lies inside the collision support; and the
orbit of a sheet has as many elements as the ramification index of the place it cuts out.  Together:

```text
nat_eq_one_of_eq_mul_self
criticalSchurInertiaAction_eq_self_of_notMem_collisionSupport
    ** a sheet outside the collision support is fixed by the whole Schur inertia group **
criticalSheetRamificationIdx_eq_one_of_notMem_collisionSupport
    ** and therefore sits over an UNRAMIFIED place **
```

The second is the first genuinely arithmetic consequence of the orbit formula: the geometric fact
that two sheets collide is turned into the arithmetic fact that a place ramifies, in the direction
that the collision count needs.  Everything ramified is a collision, so bounding the collision
support is the same problem as bounding the total ramification, which is what the different
controls.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing
open scoped Pointwise

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

theorem nat_eq_one_of_eq_mul_self {a b : ℕ} (ha : 0 < a) (h : a = b * a) : b = 1 :=
  Nat.eq_of_mul_eq_mul_right ha (by rw [one_mul]; exact h.symm)

/-- **Inertia fixes every sheet outside the collision support.** -/
theorem criticalSchurInertiaAction_eq_self_of_notMem_collisionSupport
    (hm : 1 < m) (hn : 1 < n) [DecidableEq (criticalGeometricSheet K m n)]
    {σ : criticalGeometricSheet K m n}
    (hσ : σ ∉ collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn))
    (g : criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) :
    criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ = σ := by
  haveI : Finite (criticalGeometricSheet K m n) := finite_criticalGeometricSheet K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  haveI : Fintype (criticalGeometricSheet K m n) := Fintype.ofFinite _
  by_contra hne
  refine hσ ?_
  refine permSupport_subset_collisionSupport
    (criticalGeometricSheetToSchurReducedFibre K hm hn)
    (criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g)
    (fun x => criticalGeometricSheetToSchurReducedFibre_inertia_invariant K hm hn g x) ?_
  exact Equiv.Perm.mem_support.mpr hne

/-- **Ramification of the horizon is concentrated on the collision support.**  A sheet outside the
collision support sits over an unramified place. -/
theorem criticalSheetRamificationIdx_eq_one_of_notMem_collisionSupport
    (hm : 1 < m) (hn : 1 < n) [DecidableEq (criticalGeometricSheet K m n)]
    {σ : criticalGeometricSheet K m n}
    (hσ : σ ∉ collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)) :
    (ValuationInertia.intermediateCentre (AlgHom.fieldRange σ)
        (criticalNormalClosureSchurValuationSubring K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))
        (criticalSchurNormalBase_algebraMap_mem K
          (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))).ramificationIdx
      (CriticalSchurNormalBaseRing K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) = 1 := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  haveI : Finite (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
    criticalNormalClosure K m n) := inferInstance
  have hall : ∀ g : criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn),
      criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ = σ :=
    fun g => criticalSchurInertiaAction_eq_self_of_notMem_collisionSupport K hm hn hσ g
  have hcard : Nat.card {g : (criticalNormalClosureSchurValuationSubring K
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)).inertiaSubgroup
        (criticalObservationField K m n) //
      criticalSchurInertiaAction K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) g σ = σ}
      = Nat.card (criticalSchurInertiaGroup K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv hall)
  have hfor := natCard_criticalSchurInertiaGroup_eq_sheet_mul K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ
  rw [hcard] at hfor
  have hpos : 0 < Nat.card (criticalSchurInertiaGroup K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) := Nat.card_pos
  exact nat_eq_one_of_eq_mul_self hpos hfor

end

end GaloisForLFunctions.HTGeometry
