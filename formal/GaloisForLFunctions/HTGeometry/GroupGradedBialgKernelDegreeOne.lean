import GaloisForLFunctions.HTGeometry.GroupGradedSymmetricCoalgebraFiltration
import GaloisForLFunctions.HTGeometry.ShiftInvariantDescent

/-!
# Degree-one witness in a nontrivial group-graded bialgebra kernel

Over characteristic zero, a noninjective bialgebra morphism out of `Sym(V)[M]` already has a
nonzero kernel element of additive degree at most one.  Minimal additive degree and an ambient
linear extension of the degree-one source functionals reduce every higher-degree witness by an
exact partial derivative.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace GroupGradedBialgKernelDegreeOne

noncomputable section

open GroupGradedSymmetricDegree
open GroupGradedSymmetricCoalgebraFiltration

variable {k V ι M H : Type*} [Field k] [CharZero k]
  [AddCommGroup V] [Module k V] [AddCommGroup M]
  [CommRing H] [HopfAlgebra k H]

omit [CharZero k] in
/-- Every ambient right slice of the coproduct of a kernel element remains in the kernel. -/
theorem rightSlice_comul_mem_ker
    (f : AddMonoidAlgebra (SymmetricAlgebra k V) M →ₐc[k] H)
    (φ : H →ₗ[k] k)
    {p : AddMonoidAlgebra (SymmetricAlgebra k V) M}
    (hp : p ∈ LinearMap.ker f.toLinearMap) :
    rightSlice (φ.comp f.toLinearMap) (Coalgebra.comul (R := k) p) ∈
      LinearMap.ker f.toLinearMap := by
  change f (rightSlice (φ.comp f.toLinearMap)
    (Coalgebra.comul (R := k) p)) = 0
  change f.toLinearMap (rightSlice (φ.comp f.toLinearMap)
    (Coalgebra.comul (R := k) p)) = 0
  rw [← rightSlice_map f.toLinearMap φ]
  have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f) p
  change TensorProduct.map f.toLinearMap f.toLinearMap
      (Coalgebra.comul (R := k) p) = Coalgebra.comul (R := k) (f p) at hmap
  rw [hmap]
  change f p = 0 at hp
  rw [hp, map_zero]
  simp [rightSlice]

/-- Noninjectivity is witnessed in additive degree at most one. -/
theorem exists_nonzero_ker_additiveDegree_le_one
    (basis : Module.Basis ι k V)
    (f : AddMonoidAlgebra (SymmetricAlgebra k V) M →ₐc[k] H)
    (hf : ¬ Function.Injective f) :
    ∃ p : AddMonoidAlgebra (SymmetricAlgebra k V) M,
      f p = 0 ∧ p ≠ 0 ∧ additiveDegree basis p ≤ 1 := by
  classical
  let W := LinearMap.ker f.toLinearMap
  have hW : W ≠ ⊥ := by
    rw [ne_eq, LinearMap.ker_eq_bot]
    exact hf
  obtain ⟨p, hpW, hp0, hminimal⟩ :=
    Submodule.exists_minimal_additiveDegree_ne_zero basis hW
  let D := additiveDegree basis p
  by_cases hD : D ≤ 1
  · exact ⟨p, hpW, hp0, hD⟩
  · have hDtwo : 2 ≤ D := by omega
    have hinjOne : Function.Injective
        (f.toLinearMap.domRestrict (degreeLE basis 1)) := by
      intro x y hxy
      apply Subtype.ext
      by_contra hval
      have hdiff0 : (x.1 - y.1 : AddMonoidAlgebra
          (SymmetricAlgebra k V) M) ≠ 0 := sub_ne_zero.mpr hval
      have hdiffW : x.1 - y.1 ∈ W := by
        change f (x.1 - y.1) = 0
        rw [map_sub, sub_eq_zero]
        exact hxy
      have hdiffDeg : additiveDegree basis (x.1 - y.1) ≤ 1 := by
        exact (degreeLE basis 1).sub_mem x.2 y.2
      have hmin := hminimal hdiffW hdiff0
      change D ≤ additiveDegree basis (x.1 - y.1) at hmin
      omega
    let fOne : (degreeLE basis 1) →ₗ[k] H :=
      f.toLinearMap.domRestrict (degreeLE basis 1)
    have hinjOne' : Function.Injective fOne := by
      simpa [fOne] using hinjOne
    have hfOneKer : fOne.ker = ⊥ := by
      ext x
      constructor
      · intro hx
        change fOne x = 0 at hx
        have hx0 : x = 0 := hinjOne' (hx.trans (map_zero fOne).symm)
        simp [hx0]
      · intro hx
        change x = 0 at hx
        subst x
        simp
    obtain ⟨l, hl⟩ := @LinearMap.exists_leftInverse_of_injective
      k (degreeLE basis 1) H inferInstance inferInstance inferInstance
        inferInstance inferInstance fOne hfOneKer
    obtain ⟨m, hm, hmdeg⟩ := exists_weight_additiveDegree_eq basis hp0
    have hPpos : 1 ≤ (coefficientPolynomial basis p m).totalDegree := by
      rw [hmdeg]
      omega
    obtain ⟨i, hideg⟩ := GaloisForLFunctions.exists_pderiv_totalDegree_eq
      (K := k) hPpos
    let χ := weightLinearCoefficient basis m i
    let χOne : (degreeLE basis 1) →ₗ[k] k :=
      χ.comp (degreeLE basis 1).subtype
    let φ : H →ₗ[k] k := χOne.comp l
    let ψ : AddMonoidAlgebra (SymmetricAlgebra k V) M →ₗ[k] k :=
      φ.comp f.toLinearMap
    have hagree (x : AddMonoidAlgebra (SymmetricAlgebra k V) M)
        (hx : x ∈ degreeLE basis 1) : ψ x = χ x := by
      have hlx := DFunLike.congr_fun hl (⟨x, hx⟩ : degreeLE basis 1)
      have hlx' : l (f.toLinearMap x) = (⟨x, hx⟩ : degreeLE basis 1) := by
        simpa [fOne] using hlx
      change χ ((l (f.toLinearMap x) : degreeLE basis 1).1) = χ x
      rw [hlx']
    have hgroup : ∀ a : M,
        ψ (AddMonoidAlgebra.single a (1 : SymmetricAlgebra k V)) =
          χ (AddMonoidAlgebra.single a 1) := by
      intro a
      apply hagree
      rw [mem_degreeLE_iff, additiveDegree_single]
      simp
    have hlinear : ∀ (a : M) (j : ι),
        ψ (AddMonoidAlgebra.single a (SymmetricAlgebra.ι k V (basis j))) =
          χ (AddMonoidAlgebra.single a (SymmetricAlgebra.ι k V (basis j))) := by
      intro a j
      exact hagree _ (single_ι_basis_mem_degreeLE_one basis a j)
    let q := rightSlice ψ (Coalgebra.comul (R := k) p)
    let r := rightSlice χ (Coalgebra.comul (R := k) p)
    let e := q - r
    have hqW : q ∈ W := by
      simpa [W, q, ψ] using rightSlice_comul_mem_ker f φ hpW
    have hr : r = AddMonoidAlgebra.single m
        ((SymmetricAlgebra.equivMvPolynomial basis).symm
          (MvPolynomial.pderiv i (coefficientPolynomial basis p m))) := by
      exact rightSlice_weightLinearCoefficient_comul basis p m i
    have hrdeg : additiveDegree basis r = D - 1 := by
      rw [hr, additiveDegree_single, AlgEquiv.apply_symm_apply, hideg, hmdeg]
    have hedeg : additiveDegree basis e ≤ D - 2 := by
      by_cases he0 : e = 0
      · rw [he0, additiveDegree_zero]
        omega
      · have hedrop :=
          additiveDegree_sub_rightSlice_comul_add_two_le_of_linear_eq
            basis ψ χ hgroup hlinear p
              (by simpa [e, q, r] using he0)
        change additiveDegree basis e + 2 ≤ D at hedrop
        omega
    have hq0 : q ≠ 0 := by
      intro hqzero
      have her : e = -r := by simp [e, hqzero]
      have hedegExact : additiveDegree basis e = D - 1 := by
        rw [her, hr]
        rw [show -AddMonoidAlgebra.single m
            ((SymmetricAlgebra.equivMvPolynomial basis).symm
              (MvPolynomial.pderiv i (coefficientPolynomial basis p m))) =
            AddMonoidAlgebra.single m
              (-((SymmetricAlgebra.equivMvPolynomial basis).symm
                (MvPolynomial.pderiv i (coefficientPolynomial basis p m)))) by simp]
        rw [additiveDegree_single, map_neg, AlgEquiv.apply_symm_apply,
          MvPolynomial.totalDegree_neg, hideg, hmdeg]
      omega
    have hqdeg : additiveDegree basis q ≤ D - 1 := by
      have hqeq : q = r + e := by simp [e]
      rw [hqeq]
      exact (additiveDegree_add_le basis r e).trans
        (max_le (by omega) (by omega))
    have hminq := hminimal hqW hq0
    change D ≤ additiveDegree basis q at hminq
    omega

end
end GroupGradedBialgKernelDegreeOne
end GaloisForLFunctions.HTGeometry
