import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Leading-coefficient determinant transfer

The graded Abe construction needs no entrywise jet convergence.  It is enough
that one scalar normalization of its finite evaluation matrix converges to an
invertible leading matrix: a zero determinant before normalization would remain
zero afterwards.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Normalized determinant transfer.**  If a scalar-normalized finite matrix
converges to an invertible matrix, then the unnormalized matrices are eventually
invertible.  The scalar is allowed to vanish: only the implication
`det M = 0 → det (s • M) = 0` is used. -/
theorem eventually_det_ne_zero_of_tendsto_smul_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ → ℂ) (M : ℝ → Matrix ι ι ℂ) (A : Matrix ι ι ℂ)
    (hM : Tendsto (fun B ↦ s B • M B) atTop (nhds A))
    (hA : A.det ≠ 0) :
    ∀ᶠ B in atTop, (M B).det ≠ 0 := by
  have hdet : Tendsto (fun B ↦ (s B • M B).det) atTop (nhds A.det) := by
    change Tendsto ((fun X : Matrix ι ι ℂ ↦ X.det) ∘ fun B ↦ s B • M B)
      atTop (nhds A.det)
    simpa [Function.comp_def] using
      continuous_id.matrix_det.continuousAt.tendsto.comp hM
  have hnormalized : ∀ᶠ B in atTop, (s B • M B).det ≠ 0 :=
    hdet.eventually (eventually_ne_nhds hA)
  filter_upwards [hnormalized] with B hB hzero
  apply hB
  rw [Matrix.det_smul, hzero, mul_zero]

/-- **Graded determinant transfer.**  A degree-dependent row normalization is
often required: multiplying the `j`-th jet row by its own inverse power of the
damping parameter can converge to an invertible leading matrix even though no
single scalar normalization of all entries can.  Invertibility of the
normalized product forces invertibility of the original matrix. -/
theorem eventually_det_ne_zero_of_tendsto_left_mul_matrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S M : ℝ → Matrix ι ι ℂ) (A : Matrix ι ι ℂ)
    (hM : Tendsto (fun B ↦ S B * M B) atTop (nhds A))
    (hA : A.det ≠ 0) :
    ∀ᶠ B in atTop, (M B).det ≠ 0 := by
  have hdet : Tendsto (fun B ↦ (S B * M B).det) atTop (nhds A.det) := by
    change Tendsto ((fun X : Matrix ι ι ℂ ↦ X.det) ∘ fun B ↦ S B * M B)
      atTop (nhds A.det)
    simpa [Function.comp_def] using
      continuous_id.matrix_det.continuousAt.tendsto.comp hM
  have hnormalized : ∀ᶠ B in atTop, (S B * M B).det ≠ 0 :=
    hdet.eventually (eventually_ne_nhds hA)
  filter_upwards [hnormalized] with B hB hzero
  apply hB
  rw [Matrix.det_mul, hzero, mul_zero]

end GaloisForLFunctions.HTGeometry
