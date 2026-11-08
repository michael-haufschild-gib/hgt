import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.TupleOrientationCounts
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Independent orientation counts as determinant coefficients

An invariant support contributes its actual permutation sign to the
corresponding principal minor. A moving support has a zero row. The
principal-minor expansion therefore identifies the original orientation
cover minus base count with the coefficient of the actual permutation
determinant. Trace powers count the actual fixed points, without a
simple-spectrum assumption.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open Finset Equiv Matrix Polynomial MulAction
variable {X : Type*} [Fintype X]


/-- A finite support failing invariance contains a point whose image leaves the support. -/
theorem pointSubset_not_invariant (f : Perm X) (T : Finset X)
    (hT : ¬PointSubsetInvariant f T) : ∃ x : T, f x.val ∉ T := by
  classical
  by_contra h
  push Not at h
  let g : T → T := fun x => ⟨f x.val, h x⟩
  have hi : Function.Injective g := fun a b hab =>
    Subtype.ext (f.injective (congrArg Subtype.val hab))
  have hs : Function.Surjective g := Finite.surjective_of_injective hi
  apply hT
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hs ⟨f x, hx⟩
    have hy' : f y.val = f x := congrArg Subtype.val hy
    rw [← f.injective hy']
    exact y.property
  · intro hx
    exact h ⟨x, hx⟩

/-- An actual permutation minor is its support's intrinsic orientation, or zero if it moves. -/
theorem permutation_principal_minor (f : Perm X) (T : Finset X) :
    letI : DecidableEq X := Classical.decEq X
    ((f.permMatrix ℤ).submatrix (Subtype.val : T → X) (Subtype.val : T → X)).det =
      pointSubsetOrientation f T := by
  classical
  by_cases hT : PointSubsetInvariant f T
  · rw [pointSubsetOrientation, dif_pos hT]
    have hm : (f.permMatrix ℤ).submatrix (Subtype.val : T → X) (Subtype.val : T → X) =
        (f.subtypePerm hT).permMatrix ℤ := by
      ext i j
      simp [Matrix.submatrix_apply, Equiv.toPEquiv_apply, Subtype.ext_iff]
    rw [hm, Matrix.det_permutation]
    norm_cast
  · rw [pointSubsetOrientation, dif_neg hT]
    obtain ⟨i, hi⟩ := pointSubset_not_invariant f T hT
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    have hij : f i.val ≠ j.val := fun he => hi (he ▸ j.property)
    simp [Matrix.submatrix_apply, Equiv.toPEquiv_apply, hij]

/-- The determinant is formed from the actual finite point permutation. -/
def pointOrientationPolynomial (f : Perm X) : ℤ[X] :=
  letI : DecidableEq X := Classical.decEq X
  Matrix.det (1 + (Polynomial.X : ℤ[X]) • (f.permMatrix ℤ).map Polynomial.C)

/-- Determinant coefficients sum exactly the orientations of supports of the given size. -/
theorem pointOrientationPolynomial_coeff (f : Perm X) (n : ℕ) :
    (pointOrientationPolynomial f).coeff n =
      ∑ T : {T : Finset X // T.card = n}, pointSubsetOrientation f T.val := by
  classical
  rw [pointOrientationPolynomial, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp_rw [permutation_principal_minor]
  exact sum_subtype _ (fun T => by simp only [mem_powersetCard, subset_univ, true_and]) _

/-- The original independent arithmetic quotient counts are actual determinant coefficients. -/
theorem pointTuple_orientationCount_eq_coeff (f : Perm X) (n : ℕ) :
    letI : MulAction (Perm (Fin n)) (Fin n → X) :=
      permutationTupleAction X (Perm (Fin n)) (Fin n)
    (orientationFixedOrbitCount Perm.sign (pointTupleMap n f) : ℤ) -
      (equivariantFixedOrbits (pointTupleMap n f)).card =
        (pointOrientationPolynomial f).coeff n := by
  letI : MulAction (Perm (Fin n)) (Fin n → X) :=
    permutationTupleAction X (Perm (Fin n)) (Fin n)
  rw [pointTuple_orientationCount_sub, pointOrientationPolynomial_coeff]

/-- Every trace power of the point permutation matrix is its actual fixed-point count. -/
theorem permutation_power_trace (f : Perm X) (n : ℕ) :
    letI : DecidableEq X := Classical.decEq X
    ((f.permMatrix ℂ) ^ n).trace =
      (Nat.card {x : X // (f ^ n) x = x} : ℂ) := by
  classical
  have hm (k : ℕ) : (f.permMatrix ℂ) ^ k = (f ^ k).permMatrix ℂ := by
    induction k with
    | zero => simp only [pow_zero, Matrix.permMatrix_one]
    | succ k ih =>
      rw [pow_succ, show f ^ (k + 1) = f * f ^ k from pow_succ' f k,
        Matrix.permMatrix_mul, ih]
  rw [hm, Matrix.trace_permutation]
  rfl

#print axioms pointSubset_not_invariant
#print axioms permutation_principal_minor
#print axioms pointOrientationPolynomial_coeff
#print axioms pointTuple_orientationCount_eq_coeff
#print axioms permutation_power_trace
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
