import GaloisForLFunctions.RepresentationLifting.Trace.ProjectiveTraceDuality
import GaloisForLFunctions.HTGeometry.ProjectiveWignerSmithTomography

/-!
# Trace-dual interpretation of projective Wigner--Smith reporters

The existing projective delay panel contains exactly the information supplied
by all trace-zero matrix tests. Its reference normalization is the general
division-free pivot representative. Over the complex numbers, either family
also determines the canonical traceless delay matrix.
-/

namespace GaloisForLFunctions.RepresentationLifting

open GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- Reference-channel normalization is pivot normalization in the matrix algebra. -/
theorem projectiveDelayNormalize_eq_pivot
    (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayNormalize Q = matrixPivotRepresentative (Fin.last n) Q := by
  ext i j
  by_cases hij : i = j <;>
    simp [projectiveDelayNormalize, matrixPivotRepresentative, Matrix.one_apply, hij]

/-- The finite projective panel and all trace-zero tests have exactly the same fibers. -/
theorem projectiveDelayPanel_eq_iff_traceZero_observations
    (Q S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    projectiveDelayPanel Q = projectiveDelayPanel S ↔
      ∀ B : traceZeroMatrices ℂ (Fin (n + 1)), (Q * B.val).trace = (S * B.val).trace := by
  rw [← matrixPivotRepresentative_eq_iff_observations (Fin.last n),
    ← projectiveDelayNormalize_eq_pivot, ← projectiveDelayNormalize_eq_pivot]
  constructor
  · exact projectiveDelayPanel_eq_imp_normalize_eq
  · intro h
    funext i
    simp only [projectiveDelayPanel, h]

/-- Trace-zero tests determine the canonical traceless Wigner--Smith matrix. -/
theorem matrixTracelessPart_eq_iff_traceZero_observations
    (Q S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    matrixTracelessPart Q = matrixTracelessPart S ↔
      ∀ B : traceZeroMatrices ℂ (Fin (n + 1)), (Q * B.val).trace = (S * B.val).trace := by
  rw [← projectiveDelayPanel_eq_iff_traceZero_observations]
  constructor
  · intro h
    have hp := congrArg projectiveDelayPanel h
    simpa only [projectiveDelayPanel_tracelessPart] using hp
  · intro h
    apply projectiveDelayPanel_injective_on_trace_zero
      (matrixTracelessPart_trace Q) (matrixTracelessPart_trace S)
    simpa only [projectiveDelayPanel_tracelessPart] using h

#print axioms projectiveDelayPanel_eq_iff_traceZero_observations
#print axioms matrixTracelessPart_eq_iff_traceZero_observations

end GaloisForLFunctions.RepresentationLifting
