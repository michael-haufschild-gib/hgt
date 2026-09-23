import GaloisForLFunctions.HTGeometry.SimpleSpectrumAnalyticBranch
import GaloisForLFunctions.HTGeometry.BlockSplitEscape

/-!
# The explicit spectrum of a transverse block splitting

Turning on one transverse coupling makes the Hamiltonian block diagonal with two-by-two blocks
`[[m + d, u], [u, m - d]]`.  The characteristic determinant factors over the blocks, and each block
factor is `(λ - m)² - (d² + u²)`, so the exact spectrum is `m_z ± sqrt(d_z² + u²)`.

These explicit root paths are continuous and pass through the unsplit diagonal spectrum, so branch
identification lets them replace the abstract analytic branches: the block-split escape then applies
verbatim to the eigenvalue branches of the family.
-/

open scoped BigOperators
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- One two-by-two split block, with a complex transverse coupling. -/
def splitBlock (m d : ℝ) (u : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![((m + d : ℝ) : ℂ), u], ![u, ((m - d : ℝ) : ℂ)]]

/-- The transverse block splitting of a diagonal Hamiltonian. -/
def blockSplitMatrix (m d : Z → ℝ) (u : ℂ) : Matrix (Fin 2 × Z) (Fin 2 × Z) ℂ :=
  Matrix.blockDiagonal fun z => splitBlock (m z) (d z) u

/-- The scalar matrix is block diagonal with scalar blocks. -/
theorem scalar_eq_blockDiagonal (w : ℂ) :
    (Matrix.scalar (Fin 2 × Z) w)
      = Matrix.blockDiagonal fun _ : Z => (Matrix.scalar (Fin 2) w) := by
  ext p q
  by_cases hz : p.2 = q.2
  · by_cases hi : p.1 = q.1
    · have hpq : p = q := Prod.ext hi hz
      subst hpq
      simp [Matrix.scalar_apply, Matrix.blockDiagonal_apply]
    · have hpq : p ≠ q := fun h => hi (congrArg Prod.fst h)
      simp [Matrix.scalar_apply, Matrix.blockDiagonal_apply, hz, hi, hpq]
  · have hpq : p ≠ q := fun h => hz (congrArg Prod.snd h)
    simp [Matrix.scalar_apply, Matrix.blockDiagonal_apply, hz, hpq]

/-- The characteristic determinant of a block splitting factors over the blocks. -/
theorem matrixCharpolyRelation_blockSplitMatrix (m d : Z → ℝ) (u : ℂ) (w : ℂ) :
    matrixCharpolyRelation (blockSplitMatrix m d u, w)
      = ∏ z, (Matrix.scalar (Fin 2) w - splitBlock (m z) (d z) u).det := by
  have hsub : (Matrix.scalar (Fin 2 × Z) w) - blockSplitMatrix m d u
      = Matrix.blockDiagonal fun z => (Matrix.scalar (Fin 2) w - splitBlock (m z) (d z) u) := by
    rw [scalar_eq_blockDiagonal, blockSplitMatrix, ← Matrix.blockDiagonal_sub]
    rfl
  rw [matrixCharpolyRelation, hsub, Matrix.det_blockDiagonal]

/-- The block characteristic factor. -/
theorem det_scalar_sub_splitBlock (m d : ℝ) (u : ℂ) (w : ℂ) :
    (Matrix.scalar (Fin 2) w - splitBlock m d u).det
      = (w - (m : ℂ)) ^ (2 : ℕ) - (((d ^ (2 : ℕ) : ℝ) : ℂ) + u ^ (2 : ℕ)) := by
  have hmat : (Matrix.scalar (Fin 2) w - splitBlock m d u)
      = Matrix.of ![![w - ((m + d : ℝ) : ℂ), -u],
          ![-u, w - ((m - d : ℝ) : ℂ)]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, splitBlock, Matrix.diagonal]
  rw [hmat, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  ring

/-- **The exact block-split spectrum.**  Both block roots satisfy the characteristic relation. -/
theorem matrixCharpolyRelation_blockSplitMatrix_root (m d : Z → ℝ) (u : ℝ) (z : Z) (ε : Bool) :
    matrixCharpolyRelation (blockSplitMatrix m d (u : ℂ),
        ((m z + (if ε then -1 else 1) * Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) : ℝ) : ℂ)) = 0 := by
  classical
  rw [matrixCharpolyRelation_blockSplitMatrix]
  refine Finset.prod_eq_zero (Finset.mem_univ z) ?_
  rw [det_scalar_sub_splitBlock]
  have hnn : (0 : ℝ) ≤ d z ^ (2 : ℕ) + u ^ (2 : ℕ) := by positivity
  have hshift : ((m z + (if ε then -1 else 1) * Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) : ℝ) : ℂ)
      - ((m z : ℝ) : ℂ)
      = (((if ε then -1 else 1) * Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hshift, ← Complex.ofReal_pow]
  have hcast : (((d z ^ (2 : ℕ) : ℝ) : ℂ) + (u : ℂ) ^ (2 : ℕ)) = (((d z ^ (2 : ℕ) + u ^ (2 : ℕ) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast, ← Complex.ofReal_sub, Complex.ofReal_eq_zero]
  have hsq : Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) ^ (2 : ℕ) = d z ^ (2 : ℕ) + u ^ (2 : ℕ) := Real.sq_sqrt hnn
  cases ε with
  | false =>
      rw [if_neg (by decide : ¬ (false = true))]
      rw [one_mul, hsq]
      ring
  | true =>
      rw [if_pos rfl]
      have hneg : ((-1 : ℝ) * Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ))) ^ (2 : ℕ)
          = Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      rw [hneg, hsq]
      ring

omit [Fintype Z] [DecidableEq Z] in
/-- At the unsplit point the block spectrum is the diagonal spectrum. -/
theorem blockSplitRoot_zero (m d : Z → ℝ) (z : Z) (ε : Bool) (hd : 0 < d z) :
    (m z + (if ε then -1 else 1) * Real.sqrt (d z ^ (2 : ℕ) + 0 ^ (2 : ℕ)) : ℝ)
      = m z + (if ε then -1 else 1) * d z := by
  have hsq : Real.sqrt (d z ^ (2 : ℕ) + 0 ^ (2 : ℕ)) = d z := by
    rw [show d z ^ (2 : ℕ) + 0 ^ (2 : ℕ) = d z ^ (2 : ℕ) by ring, Real.sqrt_sq hd.le]
  rw [hsq]

omit [Fintype Z] [DecidableEq Z] in
/-- The block root paths are continuous in the splitting parameter. -/
theorem continuous_blockSplitRoot (m d : Z → ℝ) (z : Z) (ε : Bool) :
    Continuous fun u : ℝ =>
      ((m z + (if ε then -1 else 1) * Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) : ℝ) : ℂ) := by
  have hsqrt : Continuous fun u : ℝ => Real.sqrt (d z ^ (2 : ℕ) + u ^ (2 : ℕ)) :=
    Real.continuous_sqrt.comp (by fun_prop)
  exact Complex.continuous_ofReal.comp (by fun_prop)

omit [Fintype Z] in
/-- The block splitting is continuous in the splitting parameter. -/
theorem continuous_blockSplitMatrix (m d : Z → ℝ) :
    Continuous fun u : ℂ => blockSplitMatrix m d u := by
  classical
  refine continuous_matrix fun p q => ?_
  obtain ⟨i, z⟩ := p
  obtain ⟨j, z'⟩ := q
  by_cases hz : z = z'
  · subst hz
    simp only [blockSplitMatrix, Matrix.blockDiagonal_apply_eq]
    fin_cases i <;> fin_cases j <;> simp [splitBlock] <;> fun_prop
  · simp only [blockSplitMatrix, Matrix.blockDiagonal_apply, if_neg hz]
    exact continuous_const

end

end GaloisForLFunctions.HTGeometry
