import GaloisForLFunctions.HTGeometry.AffineExponentialPointClosure
import GaloisForLFunctions.HTGeometry.MixedAdditiveProjectionClassification

/-!
# Mixed affine-exponential relations on subgroup cosets

This file evaluates the two relation spaces attached to a Hopf ideal on two points whose quotient
lies in its zero locus.  Additive relations have equal linear values on the two points, and torus
relations have equal character values.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry.AffineExponentialCosetRelations

open AffineExponentialGroup AffineExponentialSubgroups
open AffineExponentialPointEvaluation AffineExponentialPointClosure
open AffineExponentialProjectionClassification
open MixedAdditiveProjectionClassification

noncomputable section

variable (k : Type*) [Field k]
variable {n : ℕ} (I : Ideal (CoordinateAlgebra k n)) [I.IsHopfIdeal k]

/-- Evaluation of an additive-linear coordinate function is its finite dot product. -/
theorem eval_additiveLinear (p : Point k n) (v : Fin n → k) :
    eval (k := k) p (additiveLinear k v) =
      additiveLinearEval (k := k) (additivePart p) v := by
  simp [additiveLinear]

/-- An additive relation has the same linear value at two points in the same subgroup coset. -/
theorem additiveLinearEval_eq_of_div_mem_zeroLocus
    (p q : Point k n)
    (hdiv : p * q⁻¹ ∈ zeroLocus I)
    {v : Fin n → k} (hv : v ∈ additiveRelationSubspace k I) :
    additiveLinearEval (k := k) (additivePart p) v =
      additiveLinearEval (k := k) (additivePart q) v := by
  have hmem : additiveLinear k v ∈ I :=
    (mem_additiveRelationSubspace_iff k I v).mp hv
  have hzero := hdiv (additiveLinear k v) hmem
  rw [eval_additiveLinear] at hzero
  simp only [additivePart_mul, additivePart_inv] at hzero
  have hzero' : ∑ i, (v i * additivePart p i - v i * additivePart q i) = 0 := by
    simpa [additiveLinearEval, mul_add, sub_eq_add_neg] using hzero
  rw [Finset.sum_sub_distrib] at hzero'
  exact sub_eq_zero.mp hzero'

/-- A torus relation has the same character value at two points in the same subgroup coset. -/
theorem torusCharacter_eq_of_div_mem_zeroLocus
    (p q : Point k n)
    (hdiv : p * q⁻¹ ∈ zeroLocus I)
    {m : Fin n →₀ ℤ} (hm : m ∈ torusRelationLattice k I) :
    (AlgebraicTorusCharacter.character (torusPart p) m : k) =
      (AlgebraicTorusCharacter.character (torusPart q) m : k) := by
  have hmem : torusRelation k m ∈ I :=
    (mem_torusRelationLattice_iff k I m).mp hm
  have hzero := hdiv (torusRelation k m) hmem
  simp only [torusRelation, map_sub, map_one, eval_torusCharacter,
    sub_eq_zero] at hzero
  rw [torusPart_mul, torusPart_inv,
    AlgebraicTorusCharacter.character_mul_point,
    AlgebraicTorusCharacter.character_inv_point] at hzero
  have hq : (AlgebraicTorusCharacter.character (torusPart q) m : k) ≠ 0 := by
    exact Units.ne_zero _
  apply (div_eq_one_iff_eq hq).mp
  simpa [div_eq_mul_inv] using hzero

end

end GaloisForLFunctions.HTGeometry.AffineExponentialCosetRelations
