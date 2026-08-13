import GaloisForLFunctions.HTGeometry.BiprojectiveHilbertBezout

/-!
# Regular-modulo witnesses for biprojective quotients

Regularity modulo an arbitrary ideal is not automatic.  This file gives its exact zero-ideal
classification, unit constructors for arbitrary ideals, and a concrete nonconstant bihomogeneous
regular element.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- **Zero-ideal regularity law.**  In the biprojective polynomial domain, multiplication by `f`
is regular modulo zero exactly when `f` is nonzero. -/
theorem isRegularModulo_bot_iff
    (K : Type*) [Field K] {m n : ℕ} (f : BiprojRing K m n) :
    IsRegularModulo K ⊥ f ↔ f ≠ 0 := by
  constructor
  · intro hreg hf
    subst f
    have hone := hreg 1 (by simp)
    simp at hone
  · intro hf g hfg
    simp only [Ideal.mem_bot] at hfg ⊢
    exact (mul_eq_zero.mp hfg).resolve_left hf

/-- One is regular modulo every ideal. -/
theorem isRegularModulo_one
    (K : Type*) [Field K] {m n : ℕ} (I : Ideal (BiprojRing K m n)) :
    IsRegularModulo K I 1 := by
  intro g hg
  simpa using hg

/-- Every unit is regular modulo every ideal. -/
theorem isRegularModulo_of_isUnit
    (K : Type*) [Field K] {m n : ℕ} (I : Ideal (BiprojRing K m n))
    {f : BiprojRing K m n} (hf : IsUnit f) : IsRegularModulo K I f := by
  intro g hfg
  exact (I.unit_mul_mem_iff_mem hf).mp hfg

/-- Every polynomial is regular modulo the total ideal. -/
theorem isRegularModulo_top
    (K : Type*) [Field K] {m n : ℕ} (f : BiprojRing K m n) :
    IsRegularModulo K ⊤ f := by
  intro g hg
  simp

/-- A concrete nonconstant polynomial of bidegree `(1,1)`. -/
noncomputable def biprojectiveCoordinateProduct
    (K : Type*) [Field K] (m n : ℕ) : BiprojRing K m n :=
  X (Sum.inl (0 : Fin (m + 1))) * X (Sum.inr (0 : Fin (n + 1)))

/-- The coordinate product is bihomogeneous of bidegree `(1,1)`. -/
theorem biprojectiveCoordinateProduct_isWeightedHomogeneous
    (K : Type*) [Field K] (m n : ℕ) :
    (biprojectiveCoordinateProduct K m n).IsWeightedHomogeneous
      biprojectiveWeight (1, 1) := by
  have hleft :
      (X (Sum.inl (0 : Fin (m + 1))) : BiprojRing K m n).IsWeightedHomogeneous
        biprojectiveWeight (1, 0) := by
    simpa [biprojectiveWeight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := K) biprojectiveWeight
        (Sum.inl (0 : Fin (m + 1)) : BiprojVar m n))
  have hright :
      (X (Sum.inr (0 : Fin (n + 1))) : BiprojRing K m n).IsWeightedHomogeneous
        biprojectiveWeight (0, 1) := by
    simpa [biprojectiveWeight] using
      (MvPolynomial.isWeightedHomogeneous_X (R := K) biprojectiveWeight
        (Sum.inr (0 : Fin (n + 1)) : BiprojVar m n))
  simpa [biprojectiveCoordinateProduct] using hleft.mul hright

/-- The coordinate product is regular modulo zero. -/
theorem isRegularModulo_biprojectiveCoordinateProduct
    (K : Type*) [Field K] (m n : ℕ) :
    IsRegularModulo K (⊥ : Ideal (BiprojRing K m n))
      (biprojectiveCoordinateProduct K m n) := by
  rw [isRegularModulo_bot_iff]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

/-- A concrete singleton regular sequence of bidegree `(1,1)`. -/
theorem biprojectiveRegularSequence_coordinateProduct
    (K : Type*) [Field K] (m n : ℕ) :
    BiprojectiveRegularSequence K [biprojectiveCoordinateProduct K m n] := by
  have hreg :
      IsRegularModulo K (Ideal.ofList []) (biprojectiveCoordinateProduct K m n) := by
    simpa using isRegularModulo_biprojectiveCoordinateProduct K m n
  simpa using BiprojectiveRegularSequence.snoc
    (BiprojectiveRegularSequence.nil (K := K))
    (biprojectiveCoordinateProduct_isWeightedHomogeneous K m n)
    hreg

end GaloisForLFunctions.HTGeometry
