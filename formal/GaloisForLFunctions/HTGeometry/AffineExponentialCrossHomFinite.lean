import GaloisForLFunctions.HTGeometry.AffineExponentialGroupHopf

/-!
# Cross-factor rigidity in arbitrary dimensions

This file upgrades the one-dimensional cross-Hom theorems to arbitrary additive vector groups and
tori.  The key theorem is stronger than the required finite-dimensional statement: over a field,
the group algebra of any additive commutative group has no nonzero primitive elements.

Consequently every algebraic-group morphism in either direction between `Gₐⁿ` and `Gₘᵐ` is
trivial, proved directly in contravariant Hopf coordinates.
-/

open scoped TensorProduct
open Coalgebra Bialgebra HopfAlgebra

namespace GaloisForLFunctions.HTGeometry
namespace AlgebraicGroupCrossHomFinite

noncomputable section

variable (k : Type*) [Field k]

/-- Hopf coordinate algebra of `Gₐⁿ`. -/
abbrev GaCoordinate (n : ℕ) := SymmetricAlgebra k (Fin n → k)

/-- Hopf coordinate algebra of `Gₘᵐ`. -/
abbrev GmCoordinate (m : ℕ) := AddMonoidAlgebra k (Fin m →₀ ℤ)

/-- Trivial Hopf-coordinate map: counit followed by unit. -/
noncomputable def trivialBialgHom {A B : Type*} [Semiring A] [Semiring B]
    [Bialgebra k A] [Bialgebra k B] : A →ₐc[k] B :=
  (Bialgebra.unitBialgHom k B).comp (Bialgebra.counitBialgHom k A)

@[simp]
theorem trivialBialgHom_apply {A B : Type*} [Semiring A] [Semiring B]
    [Bialgebra k A] [Bialgebra k B] (x : A) :
    trivialBialgHom k (A := A) (B := B) x =
      algebraMap k B (Coalgebra.counit (R := k) x) := by
  rfl

/-- Every monomial in the group algebra of an additive commutative group is a unit. -/
theorem groupMonomial_isUnit {M : Type*} [AddCommGroup M] (m : M) :
    IsUnit (AddMonoidAlgebra.single m (1 : k)) := by
  rw [isUnit_iff_exists]
  refine ⟨AddMonoidAlgebra.single (-m) 1, ?_, ?_⟩ <;>
    simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]

/-- Every group-like monomial sent from a torus coordinate algebra into an additive polynomial
coordinate algebra maps to one. -/
theorem groupMonomial_toSymmetric_one {M : Type*} [AddCommGroup M] {n : ℕ}
    (f : AddMonoidAlgebra k M →ₐc[k] GaCoordinate k n) (m : M) :
    f (AddMonoidAlgebra.single m 1) = 1 := by
  let e : GaCoordinate k n ≃ₐ[k] MvPolynomial (Fin n) k :=
    SymmetricAlgebra.equivMvPolynomial (Pi.basisFun k (Fin n))
  have hu : IsUnit (e (f (AddMonoidAlgebra.single m 1))) :=
    (groupMonomial_isUnit k m).map (e.toAlgHom.comp f.toAlgHom)
  obtain ⟨c, hc, hec⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hfc : f (AddMonoidAlgebra.single m 1) = algebraMap k (GaCoordinate k n) c := by
    apply e.injective
    simpa using hec
  have hcounit := DFunLike.congr_fun (BialgHom.counitAlgHom_comp f)
    (AddMonoidAlgebra.single m 1)
  change Coalgebra.counit (R := k) (f (AddMonoidAlgebra.single m 1)) =
    Coalgebra.counit (R := k) (AddMonoidAlgebra.single m 1 : AddMonoidAlgebra k M)
      at hcounit
  rw [hfc] at hcounit
  have hc1 : c = 1 := by simpa using hcounit
  rw [hfc, hc1, map_one]

/-- Every algebraic-group morphism from an additive vector group to a diagonalizable group is
trivial, in contravariant Hopf coordinates. -/
theorem groupAlgebraToSymmetric_eq_trivial {M : Type*} [AddCommGroup M] {n : ℕ}
    (f : AddMonoidAlgebra k M →ₐc[k] GaCoordinate k n) :
    f = trivialBialgHom k := by
  have halg : f.toAlgHom = (trivialBialgHom k).toAlgHom := by
    apply AddMonoidAlgebra.algHom_ext
    · intro m
      change f (AddMonoidAlgebra.single m 1) =
        trivialBialgHom k (AddMonoidAlgebra.single m 1)
      rw [groupMonomial_toSymmetric_one k f m]
      simp [trivialBialgHom]
    · ext
  apply BialgHom.ext
  intro x
  exact DFunLike.congr_fun halg x

/-- Coefficients of a pure tensor under the group-algebra tensor equivalence factor. -/
theorem tensorEquiv_tmul_coeff {M : Type*} [AddCommGroup M]
    (p q : AddMonoidAlgebra k M) (a b : M) :
    ((AddMonoidAlgebra.tensorEquiv k) (p ⊗ₜ[k] q)).coeff (a, b) =
      p.coeff a * q.coeff b := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp only [TensorProduct.zero_tmul, map_zero,
        AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]
  | add p₁ p₂ hp₁ hp₂ =>
      rw [TensorProduct.add_tmul, map_add, AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hp₁, hp₂]
      change p₁.coeff a * q.coeff b + p₂.coeff a * q.coeff b =
        (p₁.coeff a + p₂.coeff a) * q.coeff b
      ring
  | single x c =>
      induction q using AddMonoidAlgebra.induction_linear with
      | zero =>
          simp only [TensorProduct.tmul_zero, map_zero,
            AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, mul_zero]
      | add q₁ q₂ hq₁ hq₂ =>
          rw [TensorProduct.tmul_add, map_add, AddMonoidAlgebra.coeff_add,
            Finsupp.add_apply, hq₁, hq₂]
          change (AddMonoidAlgebra.single x c).coeff a * q₁.coeff b +
              (AddMonoidAlgebra.single x c).coeff a * q₂.coeff b =
            (AddMonoidAlgebra.single x c).coeff a * (q₁.coeff b + q₂.coeff b)
          ring
      | single y d =>
          rw [AddMonoidAlgebra.tensorEquiv_single_tmul_single]
          change (Finsupp.single (x, y) (c * d)) (a, b) =
            (Finsupp.single x c) a * (Finsupp.single y d) b
          by_cases hxa : x = a <;> by_cases hyb : y = b <;>
            simp [hxa, hyb, Prod.ext_iff]

/-- The comultiplication of a group-algebra element is supported on the diagonal. -/
theorem tensorEquiv_comul_coeff {M : Type*} [AddCommGroup M] [DecidableEq M]
    (p : AddMonoidAlgebra k M) (a b : M) :
    ((AddMonoidAlgebra.tensorEquiv k) (Coalgebra.comul (R := k) p)).coeff (a, b) =
      if a = b then p.coeff a else 0 := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero =>
      simp only [map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ite_self]
  | add p q hp hq =>
      rw [map_add, map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
      by_cases hab : a = b <;> simp [hab]
  | single x c =>
      rw [AddMonoidAlgebra.comul_single]
      simp only [CommSemiring.comul_apply, TensorProduct.map_tmul,
        AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.tensorEquiv_single_tmul_single]
      simp only [one_mul, AddMonoidAlgebra.coeff_single]
      by_cases hab : a = b <;> by_cases hxa : x = a <;> by_cases hxb : x = b <;>
        simp [hab, hxa, hxb, Prod.ext_iff]

/-- The only primitive element in the group algebra of any additive commutative group over a
field is zero. -/
theorem primitive_groupAlgebra_eq_zero {M : Type*} [AddCommGroup M]
    (p : AddMonoidAlgebra k M)
    (hp : Coalgebra.comul (R := k) p = p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] p) : p = 0 := by
  classical
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro m
  change p.coeff m = 0
  have h := congrArg
    (fun z : AddMonoidAlgebra k M ⊗[k] AddMonoidAlgebra k M =>
      ((AddMonoidAlgebra.tensorEquiv k) z).coeff (m, m)) hp
  rw [tensorEquiv_comul_coeff k p m m] at h
  simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  rw [tensorEquiv_tmul_coeff k p 1 m m,
    tensorEquiv_tmul_coeff k 1 p m m] at h
  have hone : (1 : AddMonoidAlgebra k M).coeff m = if 0 = m then 1 else 0 := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    exact Finsupp.single_apply
  rw [hone] at h
  by_cases hm : m = 0
  · subst m
    rw [if_pos rfl, mul_one, one_mul] at h
    change p.coeff 0 = p.coeff 0 + p.coeff 0 at h
    linear_combination -h
  · rw [if_neg (Ne.symm hm), mul_zero, zero_mul, add_zero] at h
    exact h

/-- Every algebraic-group morphism from a diagonalizable group to an additive vector group is
trivial, in contravariant Hopf coordinates. -/
theorem symmetricToGroupAlgebra_eq_trivial {M : Type*} [AddCommGroup M] {n : ℕ}
    (f : GaCoordinate k n →ₐc[k] AddMonoidAlgebra k M) :
    f = trivialBialgHom k := by
  have hιzero : ∀ x : Fin n → k, f (SymmetricAlgebra.ι k (Fin n → k) x) = 0 := by
    intro x
    have hmap := DFunLike.congr_fun (BialgHom.map_comp_comulAlgHom f)
      (SymmetricAlgebra.ι k (Fin n → k) x)
    change
      (Algebra.TensorProduct.map f.toAlgHom f.toAlgHom)
          (Coalgebra.comul (R := k) (SymmetricAlgebra.ι k (Fin n → k) x)) =
        Coalgebra.comul (R := k) (f (SymmetricAlgebra.ι k (Fin n → k) x)) at hmap
    rw [SymmetricAlgebra.comul_ι, map_add,
      Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one] at hmap
    apply primitive_groupAlgebra_eq_zero k
    exact hmap.symm
  have halg : f.toAlgHom = (trivialBialgHom k).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change f (SymmetricAlgebra.ι k (Fin n → k) x) =
      trivialBialgHom k (SymmetricAlgebra.ι k (Fin n → k) x)
    rw [hιzero]
    simp [trivialBialgHom]
  apply BialgHom.ext
  intro x
  exact DFunLike.congr_fun halg x

/-- `Hom(Gₐⁿ, Gₘᵐ) = 0` for all finite `n,m`. -/
theorem gaToGm_eq_trivial {n m : ℕ} (f : GmCoordinate k m →ₐc[k] GaCoordinate k n) :
    f = trivialBialgHom k := groupAlgebraToSymmetric_eq_trivial k f

/-- `Hom(Gₘᵐ, Gₐⁿ) = 0` for all finite `n,m`. -/
theorem gmToGa_eq_trivial {n m : ℕ} (f : GaCoordinate k n →ₐc[k] GmCoordinate k m) :
    f = trivialBialgHom k := symmetricToGroupAlgebra_eq_trivial k f

end
end AlgebraicGroupCrossHomFinite
end GaloisForLFunctions.HTGeometry
