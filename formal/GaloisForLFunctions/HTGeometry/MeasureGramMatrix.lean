import GaloisForLFunctions.HTGeometry.AtomicGramOffDiagonal
import GaloisForLFunctions.HTGeometry.GramPairingCauchySchwarz

/-!
# The scaled measure Gram matrix

The measure part of the Pick kernel, scaled by the height and evaluated at the nodes above the
atoms, is the pairing matrix of the scaled Cauchy kernels.

Its diagonal is the atom kernel integral, which vanishes at a node carrying no mass, and its
off-diagonal is bounded by the geometric mean of two diagonals.  Both therefore vanish with the
height, leaving no measure contribution in the limit.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The scaled measure part of the Pick Gram at the nodes above the atoms. -/
def measureGram {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (y : ℝ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun l m => ∫ t, ((y : ℂ) * ((t : ℂ) - upperNode (a l) y)⁻¹) *
    (starRingEnd ℂ) ((y : ℂ) * ((t : ℂ) - upperNode (a m) y)⁻¹) ∂ν

/-- **The measure Gram diagonal is the atom kernel integral.** -/
theorem measureGram_diagonal {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (y : ℝ) (l : Fin d)
    (hint : Integrable (fun t : ℝ => atomKernel (a l) y t) ν) :
    measureGram ν a y l l = ((∫ t, atomKernel (a l) y t ∂ν : ℝ) : ℂ) := by
  have hpt : ∀ t : ℝ,
      ((y : ℂ) * ((t : ℂ) - upperNode (a l) y)⁻¹) *
        (starRingEnd ℂ) ((y : ℂ) * ((t : ℂ) - upperNode (a l) y)⁻¹)
        = ((atomKernel (a l) y t : ℝ) : ℂ) := by
    intro t
    rw [Complex.mul_conj, ← Complex.sq_norm]
    norm_cast
    exact normSq_scaled_cauchy_eq_atomKernel (a l) y t
  rw [measureGram]
  simp only [hpt]
  exact Complex.ofRealCLM.integral_comp_comm hint

/-- **The measure Gram off-diagonal is bounded by the diagonal.**  Its squared modulus is at most the
product of the two atom kernel integrals. -/
theorem norm_measureGram_sq_le {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (y : ℝ) (l m : Fin d)
    (hfi : Integrable (fun t : ℝ => atomKernel (a l) y t) ν)
    (hgi : Integrable (fun t : ℝ => atomKernel (a m) y t) ν) :
    ‖measureGram ν a y l m‖ ^ 2 ≤
      (∫ t, atomKernel (a l) y t ∂ν) * (∫ t, atomKernel (a m) y t ∂ν) :=
  norm_scaledPairing_sq_le_atomKernel_mul hfi hgi

end

end GaloisForLFunctions.HTGeometry
