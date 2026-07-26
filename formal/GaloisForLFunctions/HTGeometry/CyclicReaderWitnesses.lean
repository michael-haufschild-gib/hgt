import GaloisForLFunctions.HTGeometry.FiniteMatrixCyclicReaderRigidity

/-!
# Cyclic readers are exactly the scalar traces

The ordinary trace is cyclic, so the cyclic-reader interface is realized; combined with the rigidity
theorem this upgrades to a classification: on a nonempty finite index set the cyclic readers are
precisely the scalar multiples of the trace.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The trace is a cyclic reader. -/
theorem matrixCyclicReader_traceLinearMap :
    MatrixCyclicReader (Matrix.traceLinearMap n ℝ ℝ) := by
  intro A B
  exact Matrix.trace_mul_comm A B

omit [DecidableEq n] in
theorem matrixCyclicReader_smul {Φ : Matrix n n ℝ →ₗ[ℝ] ℝ}
    (hΦ : MatrixCyclicReader Φ) (c : ℝ) : MatrixCyclicReader (c • Φ) := by
  intro A B
  simp only [LinearMap.smul_apply]
  rw [hΦ A B]

omit [DecidableEq n] in
theorem matrixCyclicReader_zero :
    MatrixCyclicReader (0 : Matrix n n ℝ →ₗ[ℝ] ℝ) := fun _ _ => rfl

/-- **Cyclic-reader classification.**  On a nonempty finite index set the cyclic readers are exactly
the scalar multiples of the trace. -/
theorem matrixCyclicReader_iff_exists_smul_trace [Nonempty n]
    (Φ : Matrix n n ℝ →ₗ[ℝ] ℝ) :
    MatrixCyclicReader Φ ↔ ∃ c : ℝ, Φ = c • Matrix.traceLinearMap n ℝ ℝ := by
  constructor
  · intro hΦ
    exact ⟨Φ (Matrix.single (Classical.arbitrary n) (Classical.arbitrary n) 1),
      matrixCyclicReader_eq_smul_trace Φ hΦ (Classical.arbitrary n)⟩
  · rintro ⟨c, rfl⟩
    exact matrixCyclicReader_smul matrixCyclicReader_traceLinearMap c

end GaloisForLFunctions.HTGeometry
