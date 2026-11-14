import GaloisForLFunctions.RepresentationLifting.QuadraticFunctoriality

/-!
# The quadratic sequence for square-zero differentials

The Leibniz operator `T ↦ DT + TDᵀ` descends from tensor matrices to symmetric
tensors. It commutes with polarization and kills pure squares in characteristic
two. When `D² = 0`, both induced operators square to zero. These identities make
the coordinate quadratic exact sequence compatible with infinitesimal actions.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry
variable {R ι : Type*} [CommRing R] [CharP R 2] [Fintype ι] [LinearOrder ι]

/-- The Leibniz action on the tensor square. -/
def quadraticTensorDifferential (D : Matrix ι ι R) : Module.End R (Matrix ι ι R) where
  toFun T := D * T + T * D.transpose
  map_add' T U := by simp only [mul_add, add_mul, add_add_add_comm]
  map_smul' c T := by simp [smul_add]

omit [CharP R 2] in
theorem quadraticTensorDifferential_transpose (D T : Matrix ι ι R) :
    quadraticTensorDifferential D T.transpose = (quadraticTensorDifferential D T).transpose := by
  change D * T.transpose + T.transpose * D.transpose = (D * T + T * D.transpose).transpose
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact add_comm _ _

/-- The tensor differential preserves the kernel of tensor multiplication. -/
theorem quadraticTensorDifferential_kernel (D T : Matrix ι ι R)
    (hT : tensorProjection T = 0) : tensorProjection (quadraticTensorDifferential D T) = 0 := by
  have h : T ∈ LinearMap.range (tensorNorm (ι := ι) (R := R)) := by
    rw [range_tensorNorm]
    exact hT
  obtain ⟨q, rfl⟩ := h
  obtain ⟨U, rfl⟩ := tensorProjection_surjective q
  rw [tensorNorm_projection, map_add, quadraticTensorDifferential_transpose]
  exact tensorProjection_add_transpose _

/-- The differential induced on symmetric tensors. -/
def quadraticSymmetricDifferential (D : Matrix ι ι R) : Module.End R (Sym2 ι → R) :=
  tensorProjection.comp ((quadraticTensorDifferential D).comp quadraticUpperTriangle)

/-- Tensor multiplication intertwines the tensor and symmetric differentials. -/
theorem quadraticSymmetricDifferential_projection (D T : Matrix ι ι R) :
    quadraticSymmetricDifferential D (tensorProjection T) =
      tensorProjection (quadraticTensorDifferential D T) := by
  have h : tensorProjection (quadraticUpperTriangle (tensorProjection T) - T) = 0 := by
    rw [map_sub, tensorProjection_upperTriangle, sub_self]
  have ht := quadraticTensorDifferential_kernel D _ h
  rw [map_sub, map_sub] at ht
  exact sub_eq_zero.mp ht

/-- Polarization intertwines the symmetric and tensor differentials. -/
theorem quadraticSymmetricDifferential_norm (D : Matrix ι ι R) (q : Sym2 ι → R) :
    tensorNorm (quadraticSymmetricDifferential D q) =
      quadraticTensorDifferential D (tensorNorm q) := by
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [quadraticSymmetricDifferential_projection, tensorNorm_projection, tensorNorm_projection,
    map_add, quadraticTensorDifferential_transpose]

/-- The infinitesimal action on the Frobenius-twisted pure-square submodule is zero. -/
theorem quadraticSymmetricDifferential_squareDiagonal (D : Matrix ι ι R) (x : ι → R) :
    quadraticSymmetricDifferential D (squareDiagonal x) = 0 := by
  rw [← tensorProjection_diagonal, quadraticSymmetricDifferential_projection]
  change tensorProjection (D * Matrix.diagonal x + Matrix.diagonal x * D.transpose) = 0
  have ht : (D * Matrix.diagonal x).transpose = Matrix.diagonal x * D.transpose := by
    rw [Matrix.transpose_mul]
    simp
  rw [← ht]
  exact tensorProjection_add_transpose _

/-- The two cross terms cancel, so a square-zero operator stays square-zero on tensors. -/
theorem quadraticTensorDifferential_sq (D : Matrix ι ι R) (hD : D * D = 0)
    (T : Matrix ι ι R) :
    quadraticTensorDifferential D (quadraticTensorDifferential D T) = 0 := by
  have ht : D.transpose * D.transpose = 0 := by
    rw [← Matrix.transpose_mul, hD, Matrix.transpose_zero]
  have hl : D * (D * T) = 0 := by rw [← mul_assoc, hD, zero_mul]
  have hr : T * D.transpose * D.transpose = 0 := by rw [mul_assoc, ht, mul_zero]
  change D * (D * T + T * D.transpose) + (D * T + T * D.transpose) * D.transpose = 0
  rw [mul_add, add_mul, hl, hr, zero_add, add_zero, ← mul_assoc]
  ext i j
  exact CharTwo.add_self_eq_zero _

/-- Square-zero descends to symmetric tensors. -/
theorem quadraticSymmetricDifferential_sq (D : Matrix ι ι R) (hD : D * D = 0)
    (q : Sym2 ι → R) :
    quadraticSymmetricDifferential D (quadraticSymmetricDifferential D q) = 0 := by
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [quadraticSymmetricDifferential_projection, quadraticSymmetricDifferential_projection,
    quadraticTensorDifferential_sq D hD, map_zero]

/-- The induced differential satisfies the Leibniz rule on symmetric products. -/
theorem quadraticSymmetricDifferential_pair (D : Matrix ι ι R) (x y : ι → R) :
    quadraticSymmetricDifferential D (symmetricPairCoordinates x y) =
      symmetricPairCoordinates (D.mulVec x) y + symmetricPairCoordinates x (D.mulVec y) := by
  rw [← tensorProjection_vecMulVec, quadraticSymmetricDifferential_projection]
  have ht : quadraticTensorDifferential D (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (D.mulVec x) y + Matrix.vecMulVec x (D.mulVec y) := by
    simp [quadraticTensorDifferential, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose]
  rw [ht, map_add, tensorProjection_vecMulVec, tensorProjection_vecMulVec]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricDifferential_sq
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricDifferential_squareDiagonal
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricDifferential_pair
