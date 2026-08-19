import GaloisForLFunctions.HTGeometry.KaehlerJacobianRamification

/-!
# Detecting ramification through a factorized Jacobian

The coordinate matrix of a family in a basis changes by right multiplication when the family is
rewritten in terms of another family:

```text
coordinate_matrix_mul :  v j = ∑ i, P i j • w i  →  [v]_b = [w]_b * P
```

so a non-unit determinant of `P` alone already obstructs spanning, whatever the intermediate family
`w` is.  This removes the need to know that `w` itself is a basis: for the horizon map, `w` is the
family of differentials of the *raw* coordinates and `P` is the raw Jacobian, while the basis `b`
belongs to whatever presentation of the local ring is available.
-/

namespace GaloisForLFunctions.HTGeometry

open KaehlerDifferential IsLocalRing

/-- Rewriting a family through another family multiplies its coordinate matrix on the right. -/
theorem coordinate_matrix_mul {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι B M) (v w : ι → M)
    (P : Matrix ι ι B) (hvw : ∀ j, v j = ∑ i, P i j • w i) :
    (Matrix.of fun i j => b.repr (v j) i)
      = (Matrix.of fun i j => b.repr (w j) i) * P := by
  ext k j
  rw [Matrix.mul_apply, Matrix.of_apply, hvw j, map_sum]
  simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A non-unit transition determinant makes the coordinate determinant a non-unit. -/
theorem not_isUnit_det_of_eq_smul_comb {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι B M) (v w : ι → M)
    (P : Matrix ι ι B) (hvw : ∀ j, v j = ∑ i, P i j • w i) (hP : ¬ IsUnit P.det) :
    ¬ IsUnit (Matrix.of fun i j => b.repr (v j) i).det := by
  intro hu
  rw [coordinate_matrix_mul b v w P hvw, Matrix.det_mul] at hu
  exact hP (isUnit_of_mul_isUnit_right hu)

/-- **Ramification from a factorized Jacobian.**  If the differentials of the base generators are
combinations of an auxiliary family through a matrix whose determinant is not a unit, the extension
ramifies. -/
theorem map_maximalIdeal_le_sq_of_factorized_jacobian
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsLocalRing A] [IsDomain B] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι B Ω[B⁄k]) (y : ι → A)
    (w : ι → Ω[B⁄k]) (P : Matrix ι ι B)
    (hgen : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a)
      ∈ Submodule.span B (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))))
    (hvw : ∀ j, KaehlerDifferential.D k B (algebraMap A B (y j)) = ∑ i, P i j • w i)
    (hP : ¬ IsUnit P.det)
    (hbot : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
    (maximalIdeal A).map (algebraMap A B) ≤ (maximalIdeal B) ^ 2 :=
  map_maximalIdeal_le_sq_of_not_isUnit_det b y hgen
    (not_isUnit_det_of_eq_smul_comb b _ w P hvw hP) hbot

end GaloisForLFunctions.HTGeometry
