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

end Matrix
