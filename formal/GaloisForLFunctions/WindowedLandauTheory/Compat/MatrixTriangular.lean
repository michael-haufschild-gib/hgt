import Mathlib

/-!
# Triangular matrices

Upper and lower triangular square matrices as block-triangular matrices for the identity order.
-/

namespace Matrix

variable {m R : Type*} [LT m] [Zero R]

/-- `M` is upper triangular: `M i j = 0` whenever `j < i`. -/
abbrev IsUpperTriangular (M : Matrix m m R) : Prop := M.BlockTriangular id

/-- `M` is lower triangular: `M i j = 0` whenever `i < j`. -/
abbrev IsLowerTriangular (M : Matrix m m R) : Prop := M.BlockTriangular OrderDual.toDual

/-- The determinant of an upper triangular matrix is the product of its diagonal. -/
theorem det_of_isUpperTriangular {m R : Type*} [CommRing R] [Fintype m] [LinearOrder m]
    {M : Matrix m m R} (h : M.IsUpperTriangular) : M.det = ∏ i, M i i :=
  det_of_upperTriangular h

/-- The determinant of a lower triangular matrix is the product of its diagonal. -/
theorem det_of_isLowerTriangular {m R : Type*} [CommRing R] [Fintype m] [LinearOrder m]
    {M : Matrix m m R} (h : M.IsLowerTriangular) : M.det = ∏ i, M i i :=
  det_of_lowerTriangular M h

end Matrix
