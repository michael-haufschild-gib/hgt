import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Canonical inverses of identity plus a Gram operator

For every bounded operator `G`, the actual operator `1 + G*G` has a two-sided
inverse of norm at most one. A strong limit of these Gram operators therefore
gives strong convergence of their inverses, with the same uniform bound.
This is the inverse needed for the native critical genealogy reference.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open _root_.ContinuousLinearMap Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitGramOperator (G : H →L[ℂ] H) : H →L[ℂ] H := 1 + adjoint G * G

theorem unitGramOperator_coercive (G : H →L[ℂ] H) (x : H) :
    ‖x‖ ^ 2 ≤ (inner ℂ (unitGramOperator G x) x).re := by
  change ‖x‖ ^ 2 ≤ (inner ℂ (x + adjoint G (G x)) x).re
  rw [inner_add_left, adjoint_inner_left, Complex.add_re]
  change ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ x x) + RCLike.re (inner ℂ (G x) (G x))
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg ‖G x‖)

private theorem inverse_exists (G : H →L[ℂ] H) :
    ∃ R : H →L[ℂ] H, (∀ x, unitGramOperator G (R x) = x) ∧
      (∀ x, R (unitGramOperator G x) = x) ∧ ∀ x, ‖R x‖ ≤ ‖x‖ := by
  obtain ⟨R, hleft, hright, hbound⟩ := exists_inverse_of_coercive (c := 1) one_pos
    (fun x => by simpa only [one_mul] using unitGramOperator_coercive G x)
  exact ⟨R, hleft, hright, by simpa only [inv_one, one_mul] using hbound⟩

def unitGramResolvent (G : H →L[ℂ] H) : H →L[ℂ] H := (inverse_exists G).choose

@[simp] theorem unitGramOperator_resolvent_apply (G : H →L[ℂ] H) (x : H) :
    unitGramOperator G (unitGramResolvent G x) = x := (inverse_exists G).choose_spec.1 x

@[simp] theorem unitGramResolvent_operator_apply (G : H →L[ℂ] H) (x : H) :
    unitGramResolvent G (unitGramOperator G x) = x := (inverse_exists G).choose_spec.2.1 x

theorem norm_unitGramResolvent_apply_le (G : H →L[ℂ] H) (x : H) :
    ‖unitGramResolvent G x‖ ≤ ‖x‖ := (inverse_exists G).choose_spec.2.2 x

theorem norm_unitGramResolvent_le (G : H →L[ℂ] H) : ‖unitGramResolvent G‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul] using norm_unitGramResolvent_apply_le G x

theorem unitGramOperator_mul_resolvent (G : H →L[ℂ] H) :
    unitGramOperator G * unitGramResolvent G = 1 := by
  apply ContinuousLinearMap.ext
  exact unitGramOperator_resolvent_apply G

theorem unitGramResolvent_mul_operator (G : H →L[ℂ] H) :
    unitGramResolvent G * unitGramOperator G = 1 := by
  apply ContinuousLinearMap.ext
  exact unitGramResolvent_operator_apply G

theorem unitGramOperator_isUnit (G : H →L[ℂ] H) : IsUnit (unitGramOperator G) :=
  ⟨⟨unitGramOperator G, unitGramResolvent G, unitGramOperator_mul_resolvent G,
    unitGramResolvent_mul_operator G⟩, rfl⟩

theorem unitGramResolvent_difference_apply (G F : H →L[ℂ] H) (x : H) :
    unitGramResolvent F x - unitGramResolvent G x =
      unitGramResolvent F ((unitGramOperator G - unitGramOperator F) (unitGramResolvent G x)) := by
  rw [sub_apply, map_sub, unitGramOperator_resolvent_apply, unitGramResolvent_operator_apply]

theorem unitGramResolvent_strong_limit {ι : Type*} {l : Filter ι}
    (Gs : ι → H →L[ℂ] H) (G : H →L[ℂ] H)
    (hG : ∀ x, Tendsto (fun n => unitGramOperator (Gs n) x) l (𝓝 (unitGramOperator G x)))
    (x : H) :
    Tendsto (fun n => unitGramResolvent (Gs n) x) l (𝓝 (unitGramResolvent G x)) := by
  have hz : Tendsto (fun n => (unitGramOperator G - unitGramOperator (Gs n))
      (unitGramResolvent G x)) l (𝓝 0) := by
    simpa only [sub_apply, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ι => unitGramOperator G (unitGramResolvent G x)) l
        (𝓝 (unitGramOperator G (unitGramResolvent G x)))).sub (hG (unitGramResolvent G x))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa only [norm_zero] using hz.norm)
  rw [unitGramResolvent_difference_apply]
  exact norm_unitGramResolvent_apply_le _ _

end
end GaloisForLFunctions.HTGeometry
