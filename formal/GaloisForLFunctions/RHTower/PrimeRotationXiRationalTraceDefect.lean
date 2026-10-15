import GaloisForLFunctions.HTGeometry.PaperRotationRationalTraceDefect
import GaloisForLFunctions.RHTower.PrimeRotationXiBoundaryHomotopy

/-!
# The actual Xi relation's rational trace defect

For every native prime clock, compare the canonical analytic resolvent
trace with the fixed formal quantum trace on each diagonal of the actual
full singleton Xi flow matrix. Their sum equals the boundary winding of
that full matrix: full multiplicity on the right, zero on the left.

This is an integer-valued relative trace defect. It is not a constructed
K0 class, nor an assertion that its value is a projective canonical trace.
The global arithmetic transgression must account for this exact defect.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped Classical

private theorem native_clock_infinite (p : Nat.Primes) (q : ℕ) :
    ∀ b : ℤ, paperRotationPhase ((b : ℝ) * paperPrimeRotationFrequency p (q + 1)) = 1 ↔ b = 0 := by
  intro b
  simpa only [Nat.add_one_ne_zero, false_or] using paperPrimeRotationPhase_int_eq_one p (q + 1) b

private theorem xi_flow_diagonal_coordinate (p : Nat.Primes) (rho : XiDivisorSupport)
    (i : Fin (xiSupportMultiplicity rho)) :
    deningerMeyerSingleXiFlowMatrix rho (-Real.log p) i i =
      deningerMeyerPrimeMellinCoordinate p rho := by
  rw [deningerMeyerSingleXiFlowMatrix_diag]
  simp only [deningerMeyerPrimeMellinCoordinate, Complex.ofReal_neg]

/-- Relative analytic/formal trace on every actual diagonal of the full arithmetic jet relation. -/
def deningerMeyerXiRationalTraceDefect (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport) : ℂ :=
  ∑ i : Fin (xiSupportMultiplicity rho),
    paperRotationRationalTraceDefect (paperPrimeRotationFrequency p (q + 1))
      (deningerMeyerSingleXiFlowMatrix rho (-Real.log p) i i)

theorem deningerMeyerXiRationalTraceDefect_right (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport)
    (hrho : 1 / 2 < (rho : ℂ).re) :
    deningerMeyerXiRationalTraceDefect p q rho = xiSupportMultiplicity rho := by
  have h := paperRotationRationalTraceDefect_inside _ (native_clock_infinite p q)
    (deningerMeyerPrimeMellinCoordinate p rho)
    (Complex.exp_ne_zero _) (deningerMeyerPrimeMellinCoordinate_norm_lt_one p rho hrho)
  simp only [deningerMeyerXiRationalTraceDefect, xi_flow_diagonal_coordinate, h]
  simp

theorem deningerMeyerXiRationalTraceDefect_left (p : Nat.Primes) (q : ℕ) (rho : XiDivisorSupport)
    (hrho : (rho : ℂ).re < 1 / 2) :
    deningerMeyerXiRationalTraceDefect p q rho = 0 := by
  unfold deningerMeyerXiRationalTraceDefect
  simp_rw [xi_flow_diagonal_coordinate,
    paperRotationRationalTraceDefect_outside _ (native_clock_infinite p q) _
      (deningerMeyerPrimeMellinCoordinate_one_lt_norm p rho hrho)]
  simp

/-- The analytic/formal discrepancy equals the boundary degree of the literal full relation. -/
theorem deningerMeyerXiRationalTraceDefect_eq_boundary_winding (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    deningerMeyerXiRationalTraceDefect p q rho =
      (windingNumber (deningerMeyerXiRelationBoundaryLoop p rho) 0 (2 * Real.pi) : ℂ) := by
  rcases lt_or_gt_of_ne hrho with hl | hr
  · rw [deningerMeyerXiRationalTraceDefect_left p q rho hl,
      deningerMeyerXiRelationBoundaryLoop_winding_left p rho hl, Int.cast_zero]
  · rw [deningerMeyerXiRationalTraceDefect_right p q rho hr,
      deningerMeyerXiRelationBoundaryLoop_winding_right p rho hr, Int.cast_natCast]

/-- The full source discrepancy is integer-valued; it is not asserted to be a projective trace. -/
theorem deningerMeyerXiRationalTraceDefect_integer (p : Nat.Primes) (q : ℕ)
    (rho : XiDivisorSupport) (hrho : (rho : ℂ).re ≠ 1 / 2) :
    ∃ n : ℤ, deningerMeyerXiRationalTraceDefect p q rho = n :=
  ⟨_, deningerMeyerXiRationalTraceDefect_eq_boundary_winding p q rho hrho⟩

end
end RHTower
