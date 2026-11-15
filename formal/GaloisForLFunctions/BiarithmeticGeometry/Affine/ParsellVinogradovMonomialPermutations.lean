import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovMonomialCoordinates

/-!
# Coordinate permutations of the complete moment basis

Permuting physical variables preserves positive total degree and therefore
permutes the full truncated monomial basis. Horizontal permutations fix the
vertical variable. Their induced permutation of moment coordinates realizes
the inverse physical permutation exactly.
-/

open scoped BigOperators
open GaloisForLFunctions.HilbertMetric

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Permuting physical variables preserves the canonical bounded exponent set. -/
def boundedAxisPermutation (r k : ℕ) (σ : Equiv.Perm (Fin (r + 2))) :
    Equiv.Perm (BoundedAxisExponents r k) where
  toFun α := ⟨fun i => α.val (σ i), by rw [Equiv.sum_comp σ α.val]; exact α.property⟩
  invFun α := ⟨fun i => α.val (σ.symm i), by rw [Equiv.sum_comp σ.symm α.val]; exact α.property⟩
  left_inv α := by
    apply Subtype.ext
    funext i
    exact congrArg α.val (σ.apply_symm_apply i)
  right_inv α := by
    apply Subtype.ext
    funext i
    exact congrArg α.val (σ.symm_apply_apply i)

/-- A physical coordinate permutation induces a permutation of every nonconstant moment. -/
def axisIndexPermutation (r k : ℕ) (σ : Equiv.Perm (Fin (r + 2))) :
    Equiv.Perm (AffineAxisIndex r k) :=
  (axisExponentEquiv r k).trans ((boundedAxisPermutation r k σ).trans (axisExponentEquiv r k).symm)

theorem axisExponentTuple_permutation (r k : ℕ) (σ : Equiv.Perm (Fin (r + 2)))
    (a : AffineAxisIndex r k) :
    axisExponentTuple (axisIndexPermutation r k σ a) = fun i => axisExponentTuple a (σ i) :=
  congrArg Subtype.val ((axisExponentEquiv r k).apply_symm_apply
    (boundedAxisPermutation r k σ ((axisExponentEquiv r k) a)))

theorem axisIndexPermutation_symm (r k : ℕ) (σ : Equiv.Perm (Fin (r + 2))) :
    axisIndexPermutation r k σ.symm = (axisIndexPermutation r k σ).symm := by
  rfl

/-- The full nonconstant moment vector in ordinary physical-coordinate notation. -/
def canonicalMoment (r k : ℕ) (u : Fin (r + 2) → ℝ) : AffineAxisSpace r k :=
  fun a => monomialFeature axisMonomialExponent a u

theorem canonicalMoment_product (r k : ℕ) (u : Fin (r + 2) → ℝ) (a : AffineAxisIndex r k) :
    canonicalMoment r k u a = ∏ i, u i ^ axisExponentTuple a i := by
  rw [canonicalMoment, monomialFeature, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero (u i)), one_mul]
  rfl

theorem canonicalMoment_eq_affine (r k : ℕ) (u : Fin (r + 2) → ℝ) :
    canonicalMoment r k u =
      affineAxisMoment r k (fun i => u i.succ.succ) (u (Fin.succ 0)) (u 0) := by
  funext a
  exact axisMonomialFeature_eq r k a u

/-- The induced moment-coordinate permutation is exactly the inverse physical permutation. -/
theorem canonicalMoment_permutation (r k : ℕ) (σ : Equiv.Perm (Fin (r + 2)))
    (u : Fin (r + 2) → ℝ) (a : AffineAxisIndex r k) :
    canonicalMoment r k u (axisIndexPermutation r k σ a) =
      canonicalMoment r k (fun i => u (σ.symm i)) a := by
  rw [canonicalMoment_product, canonicalMoment_product, axisExponentTuple_permutation]
  have h := Equiv.prod_comp σ.symm (fun i => u i ^ axisExponentTuple a (σ i))
  simpa only [σ.apply_symm_apply] using h.symm

/-- Extend a horizontal variable permutation by fixing the vertical coordinate. -/
def horizontalVariablePermutation (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    Equiv.Perm (Fin (r + 2)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (σ.symm (σ j)).succ = j.succ
      rw [σ.symm_apply_apply]
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (σ (σ.symm j)).succ = j.succ
      rw [σ.apply_symm_apply]

theorem horizontalVariablePermutation_zero (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    horizontalVariablePermutation r σ 0 = 0 := rfl

theorem horizontalVariablePermutation_succ (r : ℕ) (σ : Equiv.Perm (Fin (r + 1)))
    (i : Fin (r + 1)) : horizontalVariablePermutation r σ i.succ = (σ i).succ := rfl

theorem horizontalVariablePermutation_symm (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) :
    horizontalVariablePermutation r σ.symm = (horizontalVariablePermutation r σ).symm := by
  rfl

/-- Moment coordinates with all horizontal variables grouped into one vector. -/
def horizontalMoment (r k : ℕ) (u : Fin (r + 1) → ℝ) (z : ℝ) : AffineAxisSpace r k :=
  canonicalMoment r k (Fin.cons z u)

theorem horizontalMoment_eq (r k : ℕ) (u : Fin (r + 1) → ℝ) (z : ℝ) :
    horizontalMoment r k u z = affineAxisMoment r k (fun i => u i.succ) (u 0) z := by
  rw [horizontalMoment, canonicalMoment_eq_affine]
  rfl

/-- The vertical variable is unchanged under the exact horizontal permutation action. -/
theorem horizontalMoment_permutation (r k : ℕ) (σ : Equiv.Perm (Fin (r + 1)))
    (u : Fin (r + 1) → ℝ) (z : ℝ) (a : AffineAxisIndex r k) :
    horizontalMoment r k u z (axisIndexPermutation r k (horizontalVariablePermutation r σ) a) =
      horizontalMoment r k (fun i => u (σ.symm i)) z a := by
  have hu : (fun i : Fin (r + 2) => (Fin.cons z u : Fin (r + 2) → ℝ)
      ((horizontalVariablePermutation r σ).symm i)) =
      (Fin.cons z (fun i : Fin (r + 1) => u (σ.symm i)) : Fin (r + 2) → ℝ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  simpa only [horizontalMoment, hu] using
    canonicalMoment_permutation r k (horizontalVariablePermutation r σ) (Fin.cons z u) a

#print axioms boundedAxisPermutation
#print axioms axisExponentTuple_permutation
#print axioms axisIndexPermutation_symm
#print axioms canonicalMoment_permutation
#print axioms horizontalVariablePermutation
#print axioms horizontalMoment_permutation

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
