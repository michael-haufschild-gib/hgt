import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelDephasingChannel

/-!
# Calibrating the damping width

The trace at a nonzero center depends only on the width and the input
trace. A unit-trace probe at center one therefore gives a width reading
independent of the Hamiltonian.
-/

open Matrix Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Read the width from the reciprocal of the unit-trace response. -/
def abelWidthFromTrace (t : ℂ) : ℝ := (-t⁻¹.im)⁻¹

theorem abelWidthFromTrace_coherence (ε : Ioi (0 : ℝ)) :
    abelWidthFromTrace (abelCoherence ε (-1)) = (ε : ℝ) := by
  unfold abelWidthFromTrace abelCoherence
  rw [inv_div, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im,
    Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  change (-((-1 : ℝ) * (ε : ℝ)⁻¹))⁻¹ = _
  rw [neg_one_mul, neg_neg, inv_inv]

/-- A basis-state preparation gives the same width reading for every
Hermitian Hamiltonian. -/
theorem abelWidthFromTrace_exact (o : Fin d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (ε : Ioi (0 : ℝ)) :
    abelWidthFromTrace
      (hamiltonianDampedGapResponse hH 1 ε (Matrix.single o o 1)).trace = (ε : ℝ) := by
  rw [trace_hamiltonianDampedGapResponse, Matrix.trace_single_eq_same, mul_one,
    abelWidthFromTrace_coherence]

/-- Equality of the calibration traces detects equality of the widths
even when the Hamiltonians differ. -/
theorem abelCalibrationTrace_eq_iff (o : Fin d)
    {H K : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (ε η : Ioi (0 : ℝ)) :
    (hamiltonianDampedGapResponse hH 1 ε (Matrix.single o o 1)).trace =
      (hamiltonianDampedGapResponse hK 1 η (Matrix.single o o 1)).trace ↔ ε = η := by
  constructor
  · intro h
    have he := congrArg abelWidthFromTrace h
    rw [abelWidthFromTrace_exact o hH ε, abelWidthFromTrace_exact o hK η] at he
    exact Subtype.ext he
  · rintro rfl
    rw [trace_hamiltonianDampedGapResponse, trace_hamiltonianDampedGapResponse]

#print axioms abelWidthFromTrace_exact
#print axioms abelCalibrationTrace_eq_iff

end

end GaloisForLFunctions.HTGeometry
