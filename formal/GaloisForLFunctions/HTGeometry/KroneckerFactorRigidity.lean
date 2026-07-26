import GaloisForLFunctions.HTGeometry.DecomposableTensorRigidity
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Rigidity of Kronecker factors

A Kronecker product is a decomposable tensor once each factor is read as a vector of its own
entries: `(A ⊗ B) (i₁, j₁) (i₂, j₂) = A i₁ i₂ · B j₁ j₂`.  The rigidity of decomposable tensors
therefore applies at the level of operators, not only of vectors: two equal Kronecker products of
nonzero matrices have proportional factors, and if one factor is literally the same on both sides
the other is determined outright.

This is the form the spectral projectors of a product grid take — `p ⊗ I` for a row split, `I ⊗ q`
for a column split, and a product of two traceless matrices for a centred checkerboard split — so
equality of two such projectors pins the local factors.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Kronecker

variable {K : Type*} [Field K] {m n : Type*}

/-- A square matrix read as a vector of its entries. -/
def matrixVec (A : Matrix m m K) : m × m → K := fun p => A p.1 p.2

theorem matrixVec_eq_zero_iff (A : Matrix m m K) : matrixVec A = 0 ↔ A = 0 := by
  constructor
  · intro h
    funext i j
    exact congrFun h (i, j)
  · intro h
    funext p
    rw [matrixVec, h]
    rfl

theorem matrixVec_ne_zero (A : Matrix m m K) (hA : A ≠ 0) : matrixVec A ≠ 0 :=
  fun h => hA ((matrixVec_eq_zero_iff A).mp h)

theorem matrixVec_one_ne_zero [Nonempty n] [DecidableEq n] :
    matrixVec (1 : Matrix n n K) ≠ 0 := by
  intro h
  have := congrFun h (Classical.arbitrary n, Classical.arbitrary n)
  simp [matrixVec] at this

/-- **A Kronecker product is a decomposable tensor in entry coordinates.** -/
theorem kronecker_eq_iff_segreTensor_eq (A A' : Matrix m m K) (B B' : Matrix n n K) :
    A ⊗ₖ B = A' ⊗ₖ B' ↔
      criticalHorizonSegreTensor (matrixVec A) (matrixVec B) =
        criticalHorizonSegreTensor (matrixVec A') (matrixVec B') := by
  constructor
  · intro h
    funext p q
    have := congrFun (congrFun h (p.1, q.1)) (p.2, q.2)
    simpa [criticalHorizonSegreTensor, matrixVec, Matrix.kroneckerMap_apply] using this
  · intro h
    funext x y
    have := congrFun (congrFun h (x.1, y.1)) (x.2, y.2)
    simpa [criticalHorizonSegreTensor, matrixVec, Matrix.kroneckerMap_apply] using this

/-- **Operator-level rigidity.**  Equal Kronecker products of nonzero matrices have proportional
factors. -/
theorem kronecker_factors_proportional {A A' : Matrix m m K} {B B' : Matrix n n K}
    (hA : A ≠ 0) (hB : B ≠ 0) (h : A ⊗ₖ B = A' ⊗ₖ B') :
    (∃ α : K, α ≠ 0 ∧ A = α • A') ∧ (∃ β : K, β ≠ 0 ∧ B = β • B') := by
  have hseg : criticalHorizonSegreTensor (matrixVec A) (matrixVec B) =
      (1 : K) • criticalHorizonSegreTensor (matrixVec A') (matrixVec B') := by
    rw [one_smul]
    exact (kronecker_eq_iff_segreTensor_eq A A' B B').mp h
  obtain ⟨α, hα, hleft⟩ :=
    criticalHorizonSegreTensor_left_line (matrixVec_ne_zero A hA) (matrixVec_ne_zero B hB) hseg
  obtain ⟨β, hβ, hright⟩ :=
    criticalHorizonSegreTensor_right_line (matrixVec_ne_zero A hA) (matrixVec_ne_zero B hB) hseg
  refine ⟨⟨α, hα, ?_⟩, ⟨β, hβ, ?_⟩⟩
  · funext i j
    have := congrFun hleft (i, j)
    simpa [matrixVec] using this
  · funext i j
    have := congrFun hright (i, j)
    simpa [matrixVec] using this

/-- **Row split.**  With the identity as the right factor on both sides, the left factor is
determined outright, not merely up to a scalar. -/
theorem kronecker_one_right_cancel [Nonempty n] [DecidableEq n] {A A' : Matrix m m K}
    (hA : A ≠ 0) (h : A ⊗ₖ (1 : Matrix n n K) = A' ⊗ₖ (1 : Matrix n n K)) :
    A = A' := by
  have hseg := (kronecker_eq_iff_segreTensor_eq A A' (1 : Matrix n n K) 1).mp h
  have hvec := criticalHorizonSegreTensor_left_cancel (matrixVec_ne_zero A hA)
    matrixVec_one_ne_zero hseg
  funext i j
  have := congrFun hvec (i, j)
  simpa [matrixVec] using this

/-- **Column split.**  Symmetrically, with the identity as the left factor the right factor is
determined outright. -/
theorem kronecker_one_left_cancel [Nonempty m] [DecidableEq m] {B B' : Matrix n n K}
    (hB : B ≠ 0) (h : (1 : Matrix m m K) ⊗ₖ B = (1 : Matrix m m K) ⊗ₖ B') :
    B = B' := by
  have hseg := (kronecker_eq_iff_segreTensor_eq (1 : Matrix m m K) 1 B B').mp h
  have hvec := criticalHorizonSegreTensor_right_cancel matrixVec_one_ne_zero
    (matrixVec_ne_zero B hB) hseg
  funext i j
  have := congrFun hvec (i, j)
  simpa [matrixVec] using this

end GaloisForLFunctions.HTGeometry
