import GaloisForLFunctions.HTGeometry.DualZLatticeCovolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gram determinants and Euclidean covolumes

For a real basis, the squared covolume of its integer span is its Gram
determinant. Orthonormal coordinates identify both quantities with the
square of an ordinary determinant. The coordinate lattice has the same
covolume and Euclidean norms.
-/

open scoped BigOperators Matrix
open Module MeasureTheory
noncomputable section
namespace GaloisForLFunctions.HTGeometry.EuclideanLattice
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

/-- An orthonormal basis with the same index set as a given basis. -/
def basisOrthonormal (b : Basis ι ℝ E) : OrthonormalBasis ι ℝ E :=
  (stdOrthonormalBasis ℝ E).reindex (Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, finrank_eq_card_basis b]))

omit [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] in
theorem gram_eq_mul_transpose (b : Basis ι ℝ E) :
    Matrix.gram ℝ b = ((basisOrthonormal b).toBasis.toMatrix b).transpose *
      (basisOrthonormal b).toBasis.toMatrix b := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simpa only [real_inner_comm (basisOrthonormal b _)] using
    ((basisOrthonormal b).sum_inner_mul_inner (b i) (b j)).symm

omit [DecidableEq ι] in
theorem orthonormal_fundamentalDomain_volume (b : OrthonormalBasis ι ℝ E) :
    volume.real (ZSpan.fundamentalDomain b.toBasis) = 1 := by
  rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b.toBasis volume)]
  change (volume (parallelepiped b)).toReal = 1
  rw [b.volume_parallelepiped, ENNReal.toReal_one]

theorem covolume_span_eq_abs_orthonormal_det (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      |((basisOrthonormal b).toBasis.toMatrix b).det| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume (b.restrictScalars ℤ)
    (basisOrthonormal b).toBasis, orthonormal_fundamentalDomain_volume, mul_one]
  congr 1
  rw [Basis.det_apply]
  congr 1
  ext i j
  simp only [Basis.toMatrix_apply, Function.comp_apply, Basis.restrictScalars_apply]

/-- The Gram determinant is the squared volume of an integral fundamental cell. -/
theorem covolume_span_sq (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 = (Matrix.gram ℝ b).det := by
  rw [covolume_span_eq_abs_orthonormal_det, gram_eq_mul_transpose,
    Matrix.det_mul, Matrix.det_transpose, sq_abs, pow_two]

/-- Covolume is the nonnegative square root of the Gram determinant. -/
theorem covolume_span_eq_sqrt_gram (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) = Real.sqrt (Matrix.gram ℝ b).det := by
  rw [← covolume_span_sq]
  exact (Real.sqrt_sq (ZLattice.covolume_pos (Submodule.span ℤ (Set.range b)) volume).le).symm

/-- Orthonormal coordinates retain the Euclidean metric. -/
def coordinates (b : Basis ι ℝ E) : E ≃ₗ[ℝ] (ι → ℝ) :=
  (basisOrthonormal b).toBasis.equivFun

/-- A basis written in orthonormal coordinates. -/
def coordinateBasis (b : Basis ι ℝ E) : Basis ι ℝ (ι → ℝ) := b.map (coordinates b)

omit [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] in
theorem norm_coordinates (b : Basis ι ℝ E) (x : E) :
    ‖WithLp.toLp 2 (coordinates b x)‖ = ‖x‖ := by
  have h : WithLp.toLp 2 (coordinates b x) = (basisOrthonormal b).repr x := by
    ext i
    exact (basisOrthonormal b).coe_toBasis_repr_apply x i
  rw [h, LinearIsometryEquiv.norm_map]

omit [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] in
theorem coordinateBasis_matrix (b : Basis ι ℝ E) :
    Matrix.of (coordinateBasis b) = ((basisOrthonormal b).toBasis.toMatrix b).transpose := by
  ext i j
  simp only [Matrix.of_apply, coordinateBasis, Basis.map_apply, coordinates,
    Matrix.transpose_apply, Basis.toMatrix_apply, Basis.equivFun_apply]

theorem covolume_coordinateBasis (b : Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range (coordinateBasis b))) =
      ZLattice.covolume (Submodule.span ℤ (Set.range b)) := by
  rw [DualZLattice.covolume_span_eq_abs_det, coordinateBasis_matrix, Matrix.det_transpose,
    covolume_span_eq_abs_orthonormal_det]

#print axioms covolume_span_eq_sqrt_gram
end GaloisForLFunctions.HTGeometry.EuclideanLattice
