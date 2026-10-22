import GaloisForLFunctions.HTGeometry.Critical.Sheet.UnramifiedOutsideCollision
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.TameInertiaCyclic
import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateField

/-!
# The Schur inertia group of the critical horizon is cyclic

`TameInertiaCyclic` proves that a finite group acting faithfully on a discrete valuation ring by ring
automorphisms, trivially on a residue field of characteristic zero, is cyclic.  The corpus had never
instantiated it.  Here are the three hypotheses on the horizon:

```text
criticalSchurInertia_faithfulSMul      faithful on the valuation ring, because every element of the
                                       normal closure is a ratio of elements of it
criticalSchurUpperResidue_charZero     the residue field receives the ground field
isCyclic_criticalSchurInertiaGroup     ** the Schur inertia group is cyclic **
```

Residual triviality is `ValuationInertiaIntermediateField.mem_inertiaSubgroup_iff`, which is the
definition of the inertia subgroup read on the ring rather than on the residue field.

With `CyclicOrbitOrderBound.natCard_le_two_of_isCyclic_of_orbit` and the orbit formula, this reduces
the order of the inertia group — hence the whole collision count — to the single question of whether
a colliding sheet sits over a place of ramification index two.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing
open scoped Pointwise

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

/-- The Schur inertia group acts faithfully on the upper Schur valuation ring. -/
instance criticalSchurInertia_faithfulSMul (hm : 0 < m) (hn : 0 < n) :
    FaithfulSMul (criticalSchurInertiaGroup K hm hn)
      (criticalNormalClosureSchurValuationSubring K hm hn) := by
  constructor
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  refine AlgEquiv.ext fun x => ?_
  rcases (criticalNormalClosureSchurValuationSubring K hm hn).mem_or_inv_mem x with hx | hx
  · exact congrArg Subtype.val (hgh ⟨x, hx⟩)
  · have h1 : ((g : criticalSchurDecompositionGroup K hm hn) :
        criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
          criticalNormalClosure K m n) x⁻¹
        = ((h : criticalSchurDecompositionGroup K hm hn) :
          criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
            criticalNormalClosure K m n) x⁻¹ :=
      congrArg Subtype.val (hgh ⟨x⁻¹, hx⟩)
    have h2 := congrArg (fun y : criticalNormalClosure K m n => y⁻¹) h1
    simpa using h2

/-- The residue field of the upper Schur place has characteristic zero. -/
instance criticalSchurUpperResidue_charZero (hm : 0 < m) (hn : 0 < n) :
    CharZero (IsLocalRing.ResidueField
      (criticalNormalClosureSchurValuationSubring K hm hn)) :=
  (RingHom.charZero_iff
    (ϕ := (IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)).comp
      ((criticalSchurObservationValuationToNormalClosure K hm hn).comp
        (criticalObservationSchurConstantBaseMap K hm hn)))
    (RingHom.injective _)).mp inferInstance

/-- **The Schur inertia group of the critical horizon is cyclic.** -/
theorem isCyclic_criticalSchurInertiaGroup (hm : 0 < m) (hn : 0 < n) :
    IsCyclic (criticalSchurInertiaGroup K hm hn) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  haveI : Finite (criticalSchurInertiaGroup K hm hn) := inferInstance
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible
      (criticalNormalClosureSchurValuationSubring K hm hn)
  refine isCyclic_of_tame (Γ := criticalSchurInertiaGroup K hm hn) hπ ?_
  intro h x
  exact ValuationInertia.smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup
    (criticalNormalClosureSchurValuationSubring K hm hn) h.property x

end

end GaloisForLFunctions.HTGeometry
