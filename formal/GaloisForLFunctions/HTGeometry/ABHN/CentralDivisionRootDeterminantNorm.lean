import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDeterminantNorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Complete root-determinant norm on a finite division algebra

For a finite division algebra `A/F`, take the positive `[A : F]`-th root of the absolute value of
the determinant of left multiplication.  The resulting norm is multiplicative, ultrametric, and
restricts exactly to the given norm on `F`.  Consequently it makes `A` a complete finite-dimensional
normed `F`-space.

This is the topological input for the approximation half of the local value--residue equality:
successive residue corrections can be taken in a complete topology intrinsic to the determinant
valuation order.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

/-- Positive `[A : F]`-th root of the determinant absolute value. -/
def divisionAlgebraRootDeterminantNorm (x : A) : ℝ :=
  ‖Algebra.norm F x‖ ^ ((Module.finrank F A : ℝ)⁻¹)

omit [CompleteSpace F] [IsUltrametricDist F] [Module.Finite F A] in
/-- The root determinant norm is nonnegative. -/
theorem divisionAlgebraRootDeterminantNorm_nonneg (x : A) :
    0 ≤ divisionAlgebraRootDeterminantNorm (F := F) x :=
  Real.rpow_nonneg (norm_nonneg _) _

/-- The root determinant norm satisfies the strong triangle inequality. -/
theorem divisionAlgebraRootDeterminantNorm_isNonarchimedean :
    IsNonarchimedean (divisionAlgebraRootDeterminantNorm (F := F) (A := A)) := by
  have hnreal : (0 : ℝ) < Module.finrank F A := by
    exact_mod_cast Module.finrank_pos (R := F) (M := A)
  have hr : 0 ≤ ((Module.finrank F A : ℝ)⁻¹) := (inv_pos.mpr hnreal).le
  intro x y
  calc
    divisionAlgebraRootDeterminantNorm (F := F) (x + y) ≤
        (max ‖Algebra.norm F x‖ ‖Algebra.norm F y‖) ^
          ((Module.finrank F A : ℝ)⁻¹) :=
      Real.rpow_le_rpow (norm_nonneg _)
        (divisionAlgebra_norm_isNonarchimedean (F := F) (A := A) x y) hr
    _ = max (divisionAlgebraRootDeterminantNorm (F := F) x)
        (divisionAlgebraRootDeterminantNorm (F := F) y) := by
      change (max ‖Algebra.norm F x‖ ‖Algebra.norm F y‖) ^
          ((Module.finrank F A : ℝ)⁻¹) =
        max (‖Algebra.norm F x‖ ^ ((Module.finrank F A : ℝ)⁻¹))
          (‖Algebra.norm F y‖ ^ ((Module.finrank F A : ℝ)⁻¹))
      rcases le_total ‖Algebra.norm F x‖ ‖Algebra.norm F y‖ with h | h
      · rw [max_eq_right h, max_eq_right
          (Real.rpow_le_rpow (norm_nonneg _) h hr)]
      · rw [max_eq_left h, max_eq_left
          (Real.rpow_le_rpow (norm_nonneg _) h hr)]

/-- Root determinant as an algebra norm extending the base-field norm exactly. -/
def divisionAlgebraRootDeterminantAlgebraNorm : AlgebraNorm F A where
  toFun := divisionAlgebraRootDeterminantNorm (F := F)
  map_zero' := by
    rw [divisionAlgebraRootDeterminantNorm, Algebra.norm_zero, norm_zero]
    have hnreal : (0 : ℝ) < Module.finrank F A := by
      exact_mod_cast Module.finrank_pos (R := F) (M := A)
    exact Real.zero_rpow (inv_ne_zero hnreal.ne')
  add_le' x y :=
    (divisionAlgebraRootDeterminantNorm_isNonarchimedean
      (F := F) (A := A) x y).trans <|
      max_le
        (le_add_of_nonneg_right (divisionAlgebraRootDeterminantNorm_nonneg (F := F) y))
        (le_add_of_nonneg_left (divisionAlgebraRootDeterminantNorm_nonneg (F := F) x))
  mul_le' x y := by
    simp only [divisionAlgebraRootDeterminantNorm]
    rw [map_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  smul' c x := by
    change divisionAlgebraRootDeterminantNorm (F := F) (c • x) =
      ‖c‖ * divisionAlgebraRootDeterminantNorm (F := F) x
    rw [divisionAlgebraRootDeterminantNorm, Algebra.smul_def, map_mul, norm_mul,
      Algebra.norm_algebraMap, norm_pow, divisionAlgebraRootDeterminantNorm,
      Real.mul_rpow (pow_nonneg (norm_nonneg _) _) (norm_nonneg _),
      Real.pow_rpow_inv_natCast (norm_nonneg _)
        (Module.finrank_pos (R := F) (M := A)).ne']
  neg' x := by
    change divisionAlgebraRootDeterminantNorm (F := F) (-x) =
      divisionAlgebraRootDeterminantNorm (F := F) x
    rw [divisionAlgebraRootDeterminantNorm, divisionAlgebraRootDeterminantNorm,
      divisionAlgebra_norm_norm_neg]
  eq_zero_of_map_eq_zero' x hx := by
    rw [divisionAlgebraRootDeterminantNorm,
      Real.rpow_eq_zero (norm_nonneg _)
        (inv_ne_zero (Nat.cast_ne_zero.mpr
          (Module.finrank_pos (R := F) (M := A)).ne'))] at hx
    exact Algebra.norm_eq_zero_iff.mp (norm_eq_zero.mp hx)

/-- Normed-ring structure induced by the root determinant.  Kept reducible so downstream proofs
can unfold its norm without installing a competing global instance. -/
@[implicit_reducible] noncomputable def divisionAlgebraRootDeterminantNormedRing : NormedRing A :=
  RingNorm.toNormedRing
    (divisionAlgebraRootDeterminantAlgebraNorm (F := F) (A := A)).toRingNorm

/-- The existing scalar action makes the root-determinant normed ring a normed `F`-space. -/
@[implicit_reducible] noncomputable def divisionAlgebraRootDeterminantNormedSpace :
    letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
    NormedSpace F A := by
  letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
  exact
    { one_smul := fun x => by simp [one_smul]
      mul_smul := fun c d x => by simp [mul_smul]
      smul_zero := fun c => by simp
      smul_add := fun c x y => by simp [smul_add]
      add_smul := fun c d x => by simp [add_smul]
      zero_smul := fun x => by simp [zero_smul]
      norm_smul_le := fun c x => by
        change divisionAlgebraRootDeterminantAlgebraNorm (F := F) (A := A) (c • x) ≤
          ‖c‖ * divisionAlgebraRootDeterminantAlgebraNorm (F := F) (A := A) x
        rw [map_smul_eq_mul] }

/-- The root-determinant metric on `A` is ultrametric. -/
theorem divisionAlgebraRootDeterminantIsUltrametricDist :
    letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
    IsUltrametricDist A := by
  letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  exact divisionAlgebraRootDeterminantNorm_isNonarchimedean (F := F) (A := A)

/-- Finite dimensionality over the complete base field makes the root-determinant topology on
`A` complete. -/
theorem divisionAlgebraRootDeterminantCompleteSpace :
    letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
    letI : NormedSpace F A :=
      divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
    CompleteSpace A := by
  letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
  letI : NormedSpace F A :=
    divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
  exact FiniteDimensional.complete F A

/-- Over a locally compact base field, the finite-dimensional root-determinant normed space is
proper.  Compact closed balls make best approximations by finite-dimensional subspaces attain
their infimum. -/
theorem divisionAlgebraRootDeterminantProperSpace [LocallyCompactSpace F] :
    letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
    letI : NormedSpace F A :=
      divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
    ProperSpace A := by
  letI : NormedRing A := divisionAlgebraRootDeterminantNormedRing (F := F) (A := A)
  letI : NormedSpace F A :=
    divisionAlgebraRootDeterminantNormedSpace (F := F) (A := A)
  exact FiniteDimensional.proper F A

end

end GaloisForLFunctions.HTGeometry.ABHN
