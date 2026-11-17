import GaloisForLFunctions.RHTower.Deninger.DeningerQ8ActualGroupRepresentation
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Square-character average of the actual quaternionic representation

The cyclic subgroup contributes zero to the square-character sum. Every
remaining quaternion element squares to the central element, which acts as
minus the identity. The normalized sum is therefore minus one, realizing the
square-character invariant in Aoki, arXiv:2611.20592, on the actual carrier.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry.GroupCharacter
open RHTower


private theorem q8_trace_identity :
    LinearMap.trace ℂ Q8Carrier (deningerQ8Representation 1) = 2 := by
  rw [map_one, LinearMap.trace_one]
  norm_num [Q8Carrier, Module.finrank_prod]

private theorem q8_trace_central :
    LinearMap.trace ℂ Q8Carrier (deningerQ8Representation (QuaternionGroup.a 2)) = -2 := by
  have h : deningerQ8Representation (QuaternionGroup.a 2) =
      -(1 : Module.End ℂ Q8Carrier) := by
    apply LinearMap.ext
    intro v
    exact deningerQ8Representation_central_apply v
  rw [h, map_neg, LinearMap.trace_one]
  norm_num [Q8Carrier, Module.finrank_prod]

private def q8SumEquiv : ZMod 4 ⊕ ZMod 4 ≃ QuaternionGroup 2 where
  toFun := Sum.elim (QuaternionGroup.a (n := 2)) (QuaternionGroup.xa (n := 2))
  invFun g := match g with
    | .a i => Sum.inl i
    | .xa i => Sum.inr i
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro (i | i) <;> rfl

/-- The literal quaternionic representation has Frobenius--Schur indicator minus one. -/
theorem q8_square_character_average :
    (Fintype.card (QuaternionGroup 2) : ℂ)⁻¹ *
      ∑ g : QuaternionGroup 2,
        LinearMap.trace ℂ Q8Carrier (deningerQ8Representation (g * g)) = -1 := by
  have ha : (∑ i : ZMod 4, LinearMap.trace ℂ Q8Carrier
      (deningerQ8Representation (QuaternionGroup.a (i + i)))) = 0 := by
    change (∑ i : Fin 4, LinearMap.trace ℂ Q8Carrier
      (deningerQ8Representation (QuaternionGroup.a ((i : ZMod 4) + (i : ZMod 4))))) = 0
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change LinearMap.trace ℂ Q8Carrier (deningerQ8Representation 1) +
      (LinearMap.trace ℂ Q8Carrier (deningerQ8Representation (QuaternionGroup.a 2)) +
      (LinearMap.trace ℂ Q8Carrier (deningerQ8Representation 1) +
      LinearMap.trace ℂ Q8Carrier (deningerQ8Representation (QuaternionGroup.a 2)))) = 0
    rw [q8_trace_identity, q8_trace_central]
    ring

  have hsum : (∑ g : QuaternionGroup 2,
      LinearMap.trace ℂ Q8Carrier (deningerQ8Representation (g * g))) = -8 := by
    calc
      _ = ∑ i : ZMod 4 ⊕ ZMod 4, LinearMap.trace ℂ Q8Carrier
          (deningerQ8Representation (q8SumEquiv i * q8SumEquiv i)) :=
        (Equiv.sum_comp q8SumEquiv _).symm
      _ = (∑ i : ZMod 4, LinearMap.trace ℂ Q8Carrier
          (deningerQ8Representation (QuaternionGroup.a (i + i)))) +
          ∑ i : ZMod 4, LinearMap.trace ℂ Q8Carrier
            (deningerQ8Representation (QuaternionGroup.a 2)) := by
        simp only [Fintype.sum_sum_type, q8SumEquiv, Equiv.coe_fn_mk, Sum.elim_inl,
          Sum.elim_inr, QuaternionGroup.a_mul_a, QuaternionGroup.xa_mul_xa,
          add_sub_cancel_right, Nat.cast_ofNat]
      _ = -8 := by rw [ha, q8_trace_central]; norm_num
  rw [hsum, QuaternionGroup.card]
  norm_num

#print axioms q8_square_character_average
end GaloisForLFunctions.HTGeometry.GroupCharacter
