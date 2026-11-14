import GaloisForLFunctions.RepresentationLifting.QuadraticNaturality

/-!
# Quadratic functoriality between different dimensions

Rectangular matrices act on symmetric tensors by descending tensor congruence
through tensor multiplication. An upper-triangular section defines the map;
preservation of the kernel proves independence of that section. This construction
recovers the existing symmetric-square action for square matrices and intertwines
polarization and Frobenius twisting for every rectangular matrix.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry
variable {R ι κ ν : Type*} [CommRing R]
  [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ] [Fintype ν] [LinearOrder ν]

/-- The tensor square of a rectangular linear map. -/
def tensorTransport (A : Matrix κ ι R) : Matrix ι ι R →ₗ[R] Matrix κ κ R where
  toFun T := A * T * A.transpose
  map_add' T U := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c T := by simp

/-- A linear section of tensor multiplication, using the upper triangle. -/
def quadraticUpperTriangle : (Sym2 ι → R) →ₗ[R] Matrix ι ι R where
  toFun q i j := if i ≤ j then q s(i, j) else 0
  map_add' q r := by
    ext i j
    by_cases h : i ≤ j <;> simp [h]
  map_smul' c q := by
    ext i j
    by_cases h : i ≤ j <;> simp [h]

omit [Fintype ι] in
theorem tensorProjection_upperTriangle (q : Sym2 ι → R) :
    tensorProjection (quadraticUpperTriangle q) = q := by
  ext a
  induction a with
  | _ i j =>
      by_cases hij : i = j
      · subst j; simp [quadraticUpperTriangle]
      · rcases lt_or_gt_of_ne hij with h | h
        · simp [quadraticUpperTriangle, hij, le_of_lt h, not_le_of_gt h]
        · simp [quadraticUpperTriangle, hij, le_of_lt h, not_le_of_gt h, Sym2.eq_swap]

variable [CharP R 2]

omit [Fintype ι] in
theorem tensorProjection_add_transpose (T : Matrix ι ι R) :
    tensorProjection (T + T.transpose) = 0 := by
  rw [← tensorNorm_projection]
  have h : tensorNorm (tensorProjection T) ∈ LinearMap.range (tensorNorm (ι := ι) (R := R)) :=
    ⟨tensorProjection T, rfl⟩
  rw [range_tensorNorm] at h
  exact h

omit [Fintype κ] in
/-- Tensor congruence preserves the kernel of tensor multiplication. -/
theorem tensorProjection_transport_zero (A : Matrix κ ι R) (T : Matrix ι ι R)
    (hT : tensorProjection T = 0) : tensorProjection (tensorTransport A T) = 0 := by
  have h : T ∈ LinearMap.range (tensorNorm (ι := ι) (R := R)) := by
    rw [range_tensorNorm]
    exact hT
  obtain ⟨q, rfl⟩ := h
  obtain ⟨U, rfl⟩ := tensorProjection_surjective q
  rw [tensorNorm_projection]
  have he : tensorTransport A (U + U.transpose) =
      tensorTransport A U + (tensorTransport A U).transpose := by
    simp only [tensorTransport, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [he]
  exact tensorProjection_add_transpose _

/-- The symmetric square of a rectangular matrix. -/
def quadraticSymmetricMap (A : Matrix κ ι R) : (Sym2 ι → R) →ₗ[R] (Sym2 κ → R) :=
  tensorProjection.comp ((tensorTransport A).comp quadraticUpperTriangle)

omit [Fintype κ] in
/-- The descended map is independent of the chosen upper-triangular representative. -/
theorem quadraticSymmetricMap_projection (A : Matrix κ ι R) (T : Matrix ι ι R) :
    quadraticSymmetricMap A (tensorProjection T) = tensorProjection (tensorTransport A T) := by
  have h : tensorProjection (quadraticUpperTriangle (tensorProjection T) - T) = 0 := by
    rw [map_sub, tensorProjection_upperTriangle, sub_self]
  have ht := tensorProjection_transport_zero A _ h
  rw [map_sub, map_sub] at ht
  exact sub_eq_zero.mp ht

/-- For square matrices, descent recovers the existing unordered-pair matrix. -/
theorem quadraticSymmetricMap_square (A : Matrix ι ι R) :
    quadraticSymmetricMap A = Matrix.toLin' (symmetricSquareMatrixGeneral A) := by
  apply LinearMap.ext
  intro q
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [quadraticSymmetricMap_projection]
  exact tensorProjection_intertwines A T

omit [LinearOrder ι] [LinearOrder κ] [Fintype ν] [LinearOrder ν] [CharP R 2] in
theorem tensorTransport_mul (A : Matrix ν κ R) (B : Matrix κ ι R) (T : Matrix ι ι R) :
    tensorTransport (A * B) T = tensorTransport A (tensorTransport B T) := by
  simp only [tensorTransport, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.transpose_mul, Matrix.mul_assoc]

omit [Fintype ν] in
/-- Symmetric squares preserve composition between arbitrary finite dimensions. -/
theorem quadraticSymmetricMap_mul (A : Matrix ν κ R) (B : Matrix κ ι R) :
    quadraticSymmetricMap (A * B) = (quadraticSymmetricMap A).comp (quadraticSymmetricMap B) := by
  apply LinearMap.ext
  intro q
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  change quadraticSymmetricMap (A * B) (tensorProjection T) =
    quadraticSymmetricMap A (quadraticSymmetricMap B (tensorProjection T))
  rw [quadraticSymmetricMap_projection, quadraticSymmetricMap_projection,
    quadraticSymmetricMap_projection, tensorTransport_mul]

omit [Fintype κ] in
/-- Polarization commutes with every rectangular linear map. -/
theorem quadraticSymmetricMap_norm (A : Matrix κ ι R) (q : Sym2 ι → R) :
    tensorNorm (quadraticSymmetricMap A q) = tensorTransport A (tensorNorm q) := by
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [quadraticSymmetricMap_projection, tensorNorm_projection, tensorNorm_projection]
  simp only [tensorTransport, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]

omit [Fintype κ] in
theorem tensorProjection_transport_diagonal (A : Matrix κ ι R) (x : ι → R) :
    tensorProjection (tensorTransport A (Matrix.diagonal x)) =
      squareDiagonal ((A.map (fun a => a ^ 2)).mulVec x) := by
  have he (i j : κ) : tensorTransport A (Matrix.diagonal x) i j =
      ∑ r, A i r * x r * A j r := by
    change (A * Matrix.diagonal x * A.transpose) i j = _
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  ext p
  induction p with
  | _ i j =>
      by_cases hij : i = j
      · subst j
        simp only [tensorProjection_mk, squareDiagonal_mk, ↓reduceIte, he,
          Matrix.mulVec, dotProduct, Matrix.map_apply]
        apply Finset.sum_congr rfl
        intro r _
        ring
      · have hs : tensorTransport A (Matrix.diagonal x) j i =
            tensorTransport A (Matrix.diagonal x) i j := by
          rw [he, he]
          apply Finset.sum_congr rfl
          intro r _
          ring
        simp only [tensorProjection_mk, squareDiagonal_mk, hij, ↓reduceIte]
        rw [hs, CharTwo.add_self_eq_zero]

omit [Fintype κ] in
/-- The pure-square submodule transforms by the entrywise Frobenius map. -/
theorem quadraticSymmetricMap_squareDiagonal (A : Matrix κ ι R) (x : ι → R) :
    quadraticSymmetricMap A (squareDiagonal x) =
      squareDiagonal ((A.map (fun a => a ^ 2)).mulVec x) := by
  rw [← tensorProjection_diagonal, quadraticSymmetricMap_projection,
    tensorProjection_transport_diagonal]

omit [Fintype κ] in
/-- Symmetric products transform as products of the transformed vectors. -/
theorem quadraticSymmetricMap_pair (A : Matrix κ ι R) (x y : ι → R) :
    quadraticSymmetricMap A (symmetricPairCoordinates x y) =
      symmetricPairCoordinates (A.mulVec x) (A.mulVec y) := by
  rw [← tensorProjection_vecMulVec, quadraticSymmetricMap_projection]
  have he : tensorTransport A (Matrix.vecMulVec x y) =
      Matrix.vecMulVec (A.mulVec x) (A.mulVec y) := by
    simp [tensorTransport, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose]
  rw [he, tensorProjection_vecMulVec]

/-- The identity matrix induces the identity on symmetric tensors. -/
theorem quadraticSymmetricMap_one :
    quadraticSymmetricMap (1 : Matrix ι ι R) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨T, rfl⟩ := tensorProjection_surjective q
  rw [quadraticSymmetricMap_projection]
  change tensorProjection (1 * T * (1 : Matrix ι ι R).transpose) = tensorProjection T
  rw [one_mul, Matrix.transpose_one, mul_one]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricMap_projection
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricMap_mul
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricMap_norm
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSymmetricMap_squareDiagonal
