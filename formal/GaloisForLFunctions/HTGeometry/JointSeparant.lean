import GaloisForLFunctions.HTGeometry.FrozenRelationDominance

/-!
# The separant as a functional of the joint jet

The separant of the frozen relation — its derivative in the top jet — is linear in the coefficients,
so as a function of the joint jet `(coefficients, jets)` it is a finite sum of coefficient values
times the corresponding monomial separants, and therefore continuous.

Continuity is what makes the separant an admissible observable of the carrier: its common vanishing
set is closed, and the flow of the line permutes the family, so minimality of the carrier forbids it
to vanish identically at any carrier point.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

variable {N n : ℕ}

/-- The separant of the frozen relation, read on the joint jet. -/
noncomputable def jointSeparant (e : Fin N → Fin (n + 1) → ℕ)
    (Y : Fin (n + 1) → ((Fin N → ℂ) × ℂ)) : ℂ :=
  partialCoeff (fderiv ℂ (frozenRelation e (Y 0).1) (fun k => (Y k).2)) (Fin.last n)

/-- The separant is the coefficient combination of the monomial separants. -/
theorem jointSeparant_eq_sum (e : Fin N → Fin (n + 1) → ℕ)
    (Y : Fin (n + 1) → ((Fin N → ℂ) × ℂ)) :
    jointSeparant e Y = ∑ i : Fin N, (Y 0).1 i *
      partialCoeff (fderiv ℂ (jetMonomial (e i)) (fun k => (Y k).2)) (Fin.last n) := by
  rw [jointSeparant, fderiv_frozenRelation]
  rw [partialCoeff]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, partialCoeff, smul_eq_mul]

theorem continuous_jointSeparant (e : Fin N → Fin (n + 1) → ℕ) :
    Continuous (jointSeparant (N := N) (n := n) e) := by
  have hrw : jointSeparant (N := N) (n := n) e = fun Y => ∑ i : Fin N, (Y 0).1 i *
      partialCoeff (fderiv ℂ (jetMonomial (e i)) (fun k => (Y k).2)) (Fin.last n) := by
    funext Y
    exact jointSeparant_eq_sum e Y
  rw [hrw]
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.mul ?_ ?_
  · exact (continuous_apply i).comp (continuous_fst.comp (continuous_apply 0))
  · have hjet : Continuous fun Y : Fin (n + 1) → ((Fin N → ℂ) × ℂ) =>
        (fun k : Fin (n + 1) => (Y k).2) :=
      continuous_pi fun k => continuous_snd.comp (continuous_apply k)
    have hpc : Continuous fun y : Fin (n + 1) → ℂ =>
        partialCoeff (fderiv ℂ (jetMonomial (e i)) y) (Fin.last n) :=
      (continuous_fderiv_jetMonomial (e i)).clm_apply continuous_const
    exact hpc.comp hjet

end GaloisForLFunctions.HTGeometry
