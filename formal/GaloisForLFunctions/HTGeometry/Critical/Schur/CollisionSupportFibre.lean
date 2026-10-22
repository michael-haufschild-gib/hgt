import GaloisForLFunctions.HTGeometry.Critical.Schur.UniqueCollisionPoint
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.PermutationCollisionInertia

/-!
# The collision support lies over a single point

`(D-f)` says any two collisions of the Schur reduction have the same reduced state, so the whole
collision support sits inside one fibre of the reduction.  Consequently the collision bound that
the transposition criterion consumes reduces to a single count: how many sheets lie over that one
point.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}
variable [Fact (0 < m)] [Fact (0 < n)] [Fact (1 < m)] [Fact (1 < n)]

/-- **The whole collision support of the Schur reduction sits over one point.** -/
theorem criticalSchur_collisionSupport_reducedFibre_eq [DecidableEq K]
    {σ τ : criticalGeometricSheet K m n}
    (hσ : σ ∈ collisionSupport
      (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n)))
    (hτ : τ ∈ collisionSupport
      (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n))) :
    criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) σ
      = criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) τ := by
  obtain ⟨y, hyne, hy⟩ := hσ
  obtain ⟨z, hzne, hz⟩ := hτ
  exact criticalSchur_reducedFibre_eq_of_collisions K σ y τ z (Ne.symm hyne) hy.symm
    (Ne.symm hzne) hz.symm

/-- **`(D)` modulo the fibre count.**  If the reduction is at most two-to-one over the single
collision point, the collision support has at most two elements. -/
theorem criticalSchur_collisionSupport_ncard_le_two_of_fibre [DecidableEq K]
    [Finite (criticalGeometricSheet K m n)]
    (hfib : ∀ σ : criticalGeometricSheet K m n,
      ({τ | criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m) (Fact.out : 1 < n) τ
        = criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m)
          (Fact.out : 1 < n) σ}).ncard ≤ 2) :
    (collisionSupport
      (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m)
        (Fact.out : 1 < n))).ncard ≤ 2 := by
  classical
  by_cases hempty : collisionSupport
      (criticalGeometricSheetToSchurReducedFibre K (Fact.out : 1 < m)
        (Fact.out : 1 < n)) = ∅
  · rw [hempty]
    simp
  · obtain ⟨σ₀, hσ₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    refine le_trans (Set.ncard_le_ncard ?_ ?_) (hfib σ₀)
    · intro τ hτ
      exact criticalSchur_collisionSupport_reducedFibre_eq K hτ hσ₀
    · exact Set.Finite.subset (Set.finite_univ) (Set.subset_univ _)

end

end GaloisForLFunctions.HTGeometry
