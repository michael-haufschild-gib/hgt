import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreMatrix
import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreColumn

/-!
# Elementary Ore row and column steps exist

An elementary step adds an operator multiple of one line of a matrix to another.  The zero
multiplier leaves the matrix unchanged, so a step from a matrix to itself exists as soon as the
index type has two distinct members — which makes the step relations reflexive there and the
equivalences they generate nonempty.
-/

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

variable {K : Type u} [Field K] [Differential K]

/-- A zero multiplier does not move the matrix. -/
theorem rowAdd_zero {ι κ : Type*} [DecidableEq ι] (i₀ k : ι) (P : ι → κ → DiffOp K) :
    rowAdd i₀ k 0 P = P := by
  funext i j
  rw [rowAdd]
  by_cases h : i = i₀
  · simp [h]
  · simp [h]

/-- **Every matrix admits an elementary row step to itself** once two indices are distinct. -/
theorem rowStep_self {ι κ : Type*} [DecidableEq ι] {i₀ k : ι} (hne : i₀ ≠ k)
    (P : ι → κ → DiffOp K) : RowStep P P :=
  ⟨i₀, k, 0, hne, (rowAdd_zero i₀ k P).symm⟩

/-- A zero multiplier does not move the matrix, in the column direction. -/
theorem colAdd_zero {ι κ : Type*} [DecidableEq κ] (j₀ k : κ) (P : ι → κ → DiffOp K) :
    colAdd j₀ k 0 P = P := by
  funext i j
  rw [colAdd]
  by_cases h : j = j₀
  · simp [h]
  · simp [h]

/-- **Every matrix admits an elementary column step to itself** once two indices are distinct. -/
theorem colStep_self {ι κ : Type*} [Fintype ι] [DecidableEq κ] {j₀ k : κ} (hne : j₀ ≠ k)
    (P : ι → κ → DiffOp K) : ColStep P P :=
  ⟨j₀, k, 0, hne, (colAdd_zero j₀ k P).symm⟩

end DiffOp

end GaloisForLFunctions.HTGeometry
