import GaloisForLFunctions.HTGeometry.GroupGradedHopfPrimitive

/-!
# Skew-primitives in group-graded symmetric Hopf algebras

Coefficient-pair extraction classifies every skew-primitive in `Sym(V)[M]`.  Equal endpoint
weights give one torus monomial times an additive-linear generator.  Distinct endpoint weights
give a scalar multiple of their group-like difference.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedSkewPrimitive

noncomputable section

variable {k B M : Type*} [Field k] [CommRing B] [Bialgebra k B]
  [AddCommGroup M] [DecidableEq M]

/-- A coefficient whose comultiplication is `x ⊗ 1` is scalar. -/
theorem eq_counit_smul_one_of_comul_eq_tmul_one
    (x : B) (hx : Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1) :
    x = Coalgebra.counit (R := k) x • 1 := by
  have h := Coalgebra.rTensor_counit_comul (R := k) x
  rw [hx] at h
  have h' := congrArg (TensorProduct.lid k B) h
  simpa using h'.symm

/-- A coefficient whose comultiplication is `1 ⊗ x` is scalar. -/
theorem eq_counit_smul_one_of_comul_eq_one_tmul
    (x : B) (hx : Coalgebra.comul (R := k) x = 1 ⊗ₜ[k] x) :
    x = Coalgebra.counit (R := k) x • 1 := by
  have h := Coalgebra.lTensor_counit_comul (R := k) x
  rw [hx] at h
  have h' := congrArg (TensorProduct.rid k B) h
  simpa using h'.symm

omit [AddCommGroup M] in
/-- A same-weight skew-primitive in `B[M]` is supported at that weight and has primitive
coefficient. -/
theorem sameWeight_skewPrimitive_eq_single_primitive
    (p : AddMonoidAlgebra B M) (a : M)
    (hp : Coalgebra.comul (R := k) p =
      p ⊗ₜ[k] AddMonoidAlgebra.single a 1 +
        AddMonoidAlgebra.single a 1 ⊗ₜ[k] p) :
    ∃ b : B,
      Coalgebra.comul (R := k) b = b ⊗ₜ[k] 1 + 1 ⊗ₜ[k] b ∧
      p = AddMonoidAlgebra.single a b := by
  have hoff : ∀ m : M, m ≠ a → p.coeff m = 0 := by
    intro m hma
    have h := congrArg (GroupGradedPrimitive.coefficientPair m m) hp
    rw [GroupGradedPrimitive.coefficientPair_comul] at h
    simp only [if_pos, map_add, GroupGradedPrimitive.coefficientPair_tmul] at h
    have hsingle : (AddMonoidAlgebra.single a (1 : B)).coeff m = 0 := by simp [hma]
    rw [hsingle] at h
    simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero] at h
    exact GroupGradedPrimitive.comul_eq_zero_imp_eq_zero (p.coeff m) h
  have ha := congrArg (GroupGradedPrimitive.coefficientPair a a) hp
  rw [GroupGradedPrimitive.coefficientPair_comul] at ha
  simp only [if_pos, map_add, GroupGradedPrimitive.coefficientPair_tmul] at ha
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at ha
  refine ⟨p.coeff a, ha, ?_⟩
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  by_cases hma : m = a
  · subst m
    simp
  · rw [hoff m hma]
    simp [hma]

omit [AddCommGroup M] in
/-- Same-weight skew-primitives in `Sym(V)[M]` are one torus monomial times one additive-linear
generator. -/
theorem sameWeight_skewPrimitive_group_symmetric_eq_single_generator
    {V ι : Type*} [AddCommGroup V] [Module k V] [CharZero k]
    (basis : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M) (a : M)
    (hp : Coalgebra.comul (R := k) p =
      p ⊗ₜ[k] AddMonoidAlgebra.single a 1 +
        AddMonoidAlgebra.single a 1 ⊗ₜ[k] p) :
    ∃ v : V, p = AddMonoidAlgebra.single a (SymmetricAlgebra.ι k V v) := by
  obtain ⟨b, hb, rfl⟩ := sameWeight_skewPrimitive_eq_single_primitive p a hp
  obtain ⟨v, rfl⟩ := SymmetricPrimitive.primitive_eq_generator k V basis b hb
  exact ⟨v, rfl⟩

/-- A skew-primitive between distinct weights in `B[M]` is a scalar multiple of their group-like
difference. -/
theorem distinctWeight_skewPrimitive_eq_smul_sub
    (p : AddMonoidAlgebra B M) (a b : M) (hab : a ≠ b)
    (hp : Coalgebra.comul (R := k) p =
      p ⊗ₜ[k] AddMonoidAlgebra.single a 1 +
        AddMonoidAlgebra.single b 1 ⊗ₜ[k] p) :
    ∃ c : k, p = c •
      (AddMonoidAlgebra.single a (1 : B) - AddMonoidAlgebra.single b 1) := by
  have hoff : ∀ m : M, m ≠ a → m ≠ b → p.coeff m = 0 := by
    intro m hma hmb
    have h := congrArg (GroupGradedPrimitive.coefficientPair m m) hp
    rw [GroupGradedPrimitive.coefficientPair_comul] at h
    simp only [if_pos, map_add, GroupGradedPrimitive.coefficientPair_tmul] at h
    have hsingleA : (AddMonoidAlgebra.single a (1 : B)).coeff m = 0 := by simp [hma]
    have hsingleB : (AddMonoidAlgebra.single b (1 : B)).coeff m = 0 := by simp [hmb]
    rw [hsingleA, hsingleB] at h
    simp only [TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero] at h
    exact GroupGradedPrimitive.comul_eq_zero_imp_eq_zero (p.coeff m) h
  have ha := congrArg (GroupGradedPrimitive.coefficientPair a a) hp
  rw [GroupGradedPrimitive.coefficientPair_comul] at ha
  simp only [if_pos, map_add, GroupGradedPrimitive.coefficientPair_tmul] at ha
  have hba : (AddMonoidAlgebra.single b (1 : B)).coeff a = 0 := by simp [hab]
  rw [hba] at ha
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    TensorProduct.zero_tmul, add_zero] at ha
  have hb := congrArg (GroupGradedPrimitive.coefficientPair b b) hp
  rw [GroupGradedPrimitive.coefficientPair_comul] at hb
  simp only [if_pos, map_add, GroupGradedPrimitive.coefficientPair_tmul] at hb
  have hab' : b ≠ a := Ne.symm hab
  have habcoeff : (AddMonoidAlgebra.single a (1 : B)).coeff b = 0 := by simp [hab']
  rw [habcoeff] at hb
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    TensorProduct.tmul_zero, zero_add] at hb
  let c : k := Coalgebra.counit (R := k) (p.coeff a)
  have hpac : p.coeff a = c • 1 :=
    eq_counit_smul_one_of_comul_eq_tmul_one (p.coeff a) ha
  let d : k := Coalgebra.counit (R := k) (p.coeff b)
  have hpbd : p.coeff b = d • 1 :=
    eq_counit_smul_one_of_comul_eq_one_tmul (p.coeff b) hb
  have hcross := congrArg (GroupGradedPrimitive.coefficientPair b a) hp
  rw [GroupGradedPrimitive.coefficientPair_comul] at hcross
  simp only [if_neg hab', map_add, GroupGradedPrimitive.coefficientPair_tmul] at hcross
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at hcross
  rw [hpac, hpbd] at hcross
  have hmap := congrArg (TensorProduct.map
    (Coalgebra.counit (R := k) (A := B))
    (Coalgebra.counit (R := k) (A := B))) hcross
  have hdc : d + c = 0 := by
    have h' := congrArg (TensorProduct.lid k k) hmap
    simpa [c, d] using h'.symm
  refine ⟨c, ?_⟩
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  by_cases hma : m = a
  · subst m
    simp [hab', hpac]
  · by_cases hmb : m = b
    · subst m
      have hdc' : d = -c := eq_neg_of_add_eq_zero_left hdc
      simp [hab, hpbd, hdc']
    · rw [hoff m hma hmb]
      simp [hma, hmb]

end
end GroupGradedSkewPrimitive
end GaloisForLFunctions.HTGeometry
