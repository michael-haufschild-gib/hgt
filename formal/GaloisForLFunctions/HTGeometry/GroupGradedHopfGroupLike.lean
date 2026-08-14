import GaloisForLFunctions.HTGeometry.GroupGradedHopfPrimitive
import GaloisForLFunctions.HTGeometry.SymmetricHopfGroupLike

/-!
# Group-like elements in group-graded Hopf algebras

A group-like element of the diagonal group-graded coalgebra `B[M]` has exactly
one nonzero homogeneous coefficient, which is itself group-like in `B`.
Consequently, the group-like elements of `Sym(V)[M]` are precisely monomials
`single m 1`.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedGroupLike

noncomputable section

variable {k B M : Type*} [Field k] [CommRing B] [Algebra k B]
  [Coalgebra k B] [AddCommGroup M] [DecidableEq M]

omit [AddCommGroup M] in
theorem coeff_comul_eq_tmul_self (p : AddMonoidAlgebra B M)
    (hp : IsGroupLikeElem k p) (m : M) :
    Coalgebra.comul (R := k) (p.coeff m) = p.coeff m ⊗ₜ[k] p.coeff m := by
  have h := congrArg (GroupGradedPrimitive.coefficientPair m m) hp.comul_eq_tmul_self
  rw [GroupGradedPrimitive.coefficientPair_comul] at h
  simpa using h

theorem counit_eq_one_of_comul_eq_tmul_self {b : B} (hb : b ≠ 0)
    (hcom : Coalgebra.comul (R := k) b = b ⊗ₜ[k] b) :
    Coalgebra.counit (R := k) b = 1 := by
  have h := Coalgebra.lTensor_counit_comul (R := k) b
  rw [hcom] at h
  have h' := congrArg (TensorProduct.rid k B) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h'
  apply smul_left_injective k hb
  simpa using h'

omit [AddCommGroup M] in
theorem coeff_isGroupLike (p : AddMonoidAlgebra B M)
    (hp : IsGroupLikeElem k p) {m : M} (hm : p.coeff m ≠ 0) :
    IsGroupLikeElem k (p.coeff m) := by
  refine ⟨?_, coeff_comul_eq_tmul_self p hp m⟩
  exact counit_eq_one_of_comul_eq_tmul_self hm (coeff_comul_eq_tmul_self p hp m)

omit [AddCommGroup M] in
theorem coeff_nonzero_unique (p : AddMonoidAlgebra B M)
    (hp : IsGroupLikeElem k p) {m n : M}
    (hm : p.coeff m ≠ 0) (hn : p.coeff n ≠ 0) : m = n := by
  by_contra hne
  have h : GroupGradedPrimitive.coefficientPair m n
      (Coalgebra.comul (R := k) p) = 0 := by
    rw [GroupGradedPrimitive.coefficientPair_comul]
    simp [hne]
  rw [hp.comul_eq_tmul_self, GroupGradedPrimitive.coefficientPair_tmul] at h
  have hmG := coeff_isGroupLike p hp hm
  have hnG := coeff_isGroupLike p hp hn
  have hmap := congrArg (TensorProduct.map
      (Coalgebra.counit (R := k) (A := B))
      (Coalgebra.counit (R := k) (A := B))) h
  simp only [TensorProduct.map_tmul, map_zero, hmG.counit_eq_one,
    hnG.counit_eq_one] at hmap
  have hc := congrArg (TensorProduct.lid k k) hmap
  simp at hc

omit [AddCommGroup M] in
/-- Every group-like element of `B[M]` is concentrated in one grade. -/
theorem groupLike_eq_single (p : AddMonoidAlgebra B M)
    (hp : IsGroupLikeElem k p) :
    ∃ m : M, ∃ b : B, IsGroupLikeElem k b ∧
      p = AddMonoidAlgebra.single m b := by
  have hex : ∃ m : M, p.coeff m ≠ 0 := by
    by_contra h
    push Not at h
    apply hp.ne_zero
    ext m
    simpa using h m
  obtain ⟨m, hm⟩ := hex
  refine ⟨m, p.coeff m, coeff_isGroupLike p hp hm, ?_⟩
  ext n
  by_cases hnm : n = m
  · subst n
    simp
  · have hn : p.coeff n = 0 := by
      by_contra hn
      exact hnm (coeff_nonzero_unique p hp hn hm)
    rw [hn]
    simp [hnm]

omit [AddCommGroup M] in
/-- Group-like elements of `Sym(V)[M]` are pure grading monomials. -/
theorem groupLike_group_symmetric_eq_monomial
    {V ι : Type*} [AddCommGroup V] [Module k V]
    (bV : Module.Basis ι k V)
    (p : AddMonoidAlgebra (SymmetricAlgebra k V) M)
    (hp : IsGroupLikeElem k p) :
    ∃ m : M, p = AddMonoidAlgebra.single m 1 := by
  obtain ⟨m, b, hb, rfl⟩ := groupLike_eq_single p hp
  rw [symmetric_groupLike_eq_one bV b hb]
  exact ⟨m, rfl⟩

end
end GroupGradedGroupLike
end GaloisForLFunctions.HTGeometry
