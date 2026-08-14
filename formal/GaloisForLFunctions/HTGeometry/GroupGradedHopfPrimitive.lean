import GaloisForLFunctions.HTGeometry.SymmetricHopfPrimitive

/-!
# Primitive elements in group-graded Hopf algebras

For a coalgebra `B` and an additive group `M`, every primitive element of the
group-graded coalgebra `B[M]` is supported at the identity of `M`, and its
identity coefficient is primitive in `B`.  Specializing `B` to a symmetric
Hopf algebra proves that the torus grading contributes no additive direction.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedPrimitive

noncomputable section

variable {k B M : Type*} [Field k] [CommSemiring B] [Algebra k B]
  [Coalgebra k B] [AddCommGroup M]

noncomputable def coefficient (m : M) : AddMonoidAlgebra B M →ₗ[k] B :=
  (Finsupp.lapply (R := k) (M := B) m).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

omit [Coalgebra k B] [AddCommGroup M] in
@[simp] theorem coefficient_apply (m : M) (p : AddMonoidAlgebra B M) :
    coefficient (k := k) (B := B) m p = p.coeff m := by
  rfl

noncomputable def coefficientPair (m n : M) :
    AddMonoidAlgebra B M ⊗[k] AddMonoidAlgebra B M →ₗ[k] B ⊗[k] B :=
  TensorProduct.map
    (coefficient (k := k) (B := B) m)
    (coefficient (k := k) (B := B) n)

omit [Coalgebra k B] [AddCommGroup M] in
@[simp] theorem coefficientPair_tmul (m n : M)
    (p q : AddMonoidAlgebra B M) :
    coefficientPair m n (p ⊗ₜ[k] q) = p.coeff m ⊗ₜ[k] q.coeff n := by
  simp [coefficientPair]

omit [Coalgebra k B] [AddCommGroup M] in
theorem coefficient_comp_lsingle [DecidableEq M] (m x : M) :
    (coefficient (k := k) (B := B) m).comp
      (AddMonoidAlgebra.lsingle (R := k) x) =
        if m = x then (LinearMap.id : B →ₗ[k] B) else 0 := by
  by_cases h : m = x
  · subst x
    ext b
    simp [coefficient]
  · rw [if_neg h]
    ext b
    simp [coefficient, h]

omit [AddCommGroup M] in
theorem coefficientPair_comul [DecidableEq M]
    (p : AddMonoidAlgebra B M) (m n : M) :
    coefficientPair m n (Coalgebra.comul (R := k) p) =
      if m = n then Coalgebra.comul (R := k) (p.coeff m) else 0 := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp [coefficientPair]
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq]
      by_cases h : m = n <;> simp [h]
  | single x b =>
      rw [AddMonoidAlgebra.comul_single]
      rw [coefficientPair, TensorProduct.map_map]
      rw [coefficient_comp_lsingle (k := k) (B := B),
        coefficient_comp_lsingle (k := k) (B := B)]
      by_cases hmx : m = x <;> by_cases hnx : n = x
      · subst m
        subst n
        simp
      · subst m
        have hxn : x ≠ n := Ne.symm hnx
        simp [hnx, hxn]
      · subst n
        simp [hmx]
      · simp [hmx, hnx]

theorem comul_eq_zero_imp_eq_zero (b : B)
    (hb : Coalgebra.comul (R := k) b = 0) : b = 0 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) b
  rw [hb, map_zero] at h
  have h' := congrArg (TensorProduct.lid k B) h
  simpa using h'.symm

theorem primitive_coeff_of_ne_zero [DecidableEq M]
    (p : AddMonoidAlgebra B M)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p)
    {m : M} (hm : m ≠ 0) : p.coeff m = 0 := by
  have h := congrArg (coefficientPair m m) hp
  rw [coefficientPair_comul] at h
  simp only [if_pos, map_add, coefficientPair_tmul] at h
  have hone : (1 : AddMonoidAlgebra B M).coeff m = 0 := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    simp [hm]
  rw [hone] at h
  simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero] at h
  exact comul_eq_zero_imp_eq_zero (p.coeff m) h

theorem primitive_zero_coeff [DecidableEq M]
    (p : AddMonoidAlgebra B M)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) :
    Coalgebra.comul (R := k) (p.coeff 0) =
      p.coeff 0 ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p.coeff 0 := by
  have h := congrArg (coefficientPair 0 0) hp
  rw [coefficientPair_comul] at h
  simpa [AddMonoidAlgebra.one_def] using h

/-- A primitive group-graded element is supported only at the identity. -/
theorem primitive_eq_single_zero [DecidableEq M]
    (p : AddMonoidAlgebra B M)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) :
    ∃ b : B,
      Coalgebra.comul (R := k) b = b ⊗ₜ[k] 1 + 1 ⊗ₜ[k] b ∧
      p = AddMonoidAlgebra.single 0 b := by
  refine ⟨p.coeff 0, primitive_zero_coeff p hp, ?_⟩
  ext m
  by_cases hm : m = 0
  · subst m
    simp
  · rw [primitive_coeff_of_ne_zero p hp hm]
    simp [hm]

/-- Primitive functions on `Gₘ × Gₐ(V)` are additive-linear. -/
theorem primitive_group_symmetric_eq_single_generator
    {V ι : Type*} [AddCommGroup V] [Module k V] [CharZero k]
    [DecidableEq M] (bV : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) :
    ∃ v : V, p = AddMonoidAlgebra.single 0 (SymmetricAlgebra.ι k V v) := by
  obtain ⟨b, hb, rfl⟩ := primitive_eq_single_zero p hp
  obtain ⟨v, rfl⟩ := SymmetricPrimitive.primitive_eq_generator k V bV b hb
  exact ⟨v, rfl⟩

end
end GroupGradedPrimitive
end GaloisForLFunctions.HTGeometry
