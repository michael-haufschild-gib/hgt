import GaloisForLFunctions.RHTower.BurnolDividedShiftSourceLeakage
import GaloisForLFunctions.RHTower.GammaCoPoissonSoninActualZeroEscape

/-!
# Burnol divided-shift/evaluation-vector separation

At a right-half-strip zeta zero, the completed-Mellin evaluation vector is orthogonal to the
closed co-Poisson source space.  Strict accretivity of the Burnol Cauchy divided shift says the
opposite for the image of every nonzero source vector: its source projection cannot vanish.

The combination gives an unconditional quantitative no-landing theorem.  Subtracting the zero
evaluation vector does not change the divided shift's source projection, and horizontal distance
to the critical line times the divided-shift energy is a lower bound for both the retained source
component and the ambient distance from the evaluator.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- A right-half-strip zeta zero's completed-Mellin evaluator has zero co-Poisson source
projection. -/
theorem burnolCoPoissonSourceProjection_evaluationVector_eq_zero_of_riemannZeta_eq_zero
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hz : riemannZeta w = 0) :
    burnolCoPoissonSourceProjection b
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) = 0 := by
  rw [burnolCoPoissonSourceProjection_eq_zero_iff]
  exact burnolExtendedSoninEvaluationVector_mem_source_orthogonal hlo hhi hb
    (burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero hlo hhi hb hz)

/-- Subtracting a zero evaluator leaves the divided shift's co-Poisson source projection
unchanged. -/
theorem burnolCoPoissonSourceProjection_mellinDividedShift_sub_evaluationVector
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hz : riemannZeta w = 0) (f : evenSubspace) :
    burnolCoPoissonSourceProjection b
        (burnolMellinDividedShift (rho := w) hlo f -
          (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)) =
      burnolCoPoissonSourceProjection b (burnolMellinDividedShift (rho := w) hlo f) := by
  rw [map_sub,
    burnolCoPoissonSourceProjection_evaluationVector_eq_zero_of_riemannZeta_eq_zero
      hlo hhi hb hz,
    sub_zero]

/-- Quantitative source separation: the evaluator subtraction retains the full strict-accretive
source leakage floor. -/
theorem burnolMellinDividedShift_sub_evaluationVector_sourceProjection_lower_bound
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hz : riemannZeta w = 0) {f : evenSubspace}
    (hfS : f ∈ burnolCoPoissonSourceSpace b) :
    (w.re - 1 / 2) * ‖burnolMellinDividedShift (rho := w) hlo f‖ ^ 2 ≤
      ‖f‖ * ‖burnolCoPoissonSourceProjection b
        (burnolMellinDividedShift (rho := w) hlo f -
          (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace))‖ := by
  rw [burnolCoPoissonSourceProjection_mellinDividedShift_sub_evaluationVector
    hlo hhi hb hz]
  exact burnolCoPoissonSourceProjection_mellinDividedShift_lower_bound hlo b hfS

/-- Ambient quantitative separation from the zero evaluator. -/
theorem burnolMellinDividedShift_sub_evaluationVector_distance_lower_bound
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hz : riemannZeta w = 0) {f : evenSubspace}
    (hfS : f ∈ burnolCoPoissonSourceSpace b) :
    (w.re - 1 / 2) * ‖burnolMellinDividedShift (rho := w) hlo f‖ ^ 2 ≤
      ‖f‖ * ‖burnolMellinDividedShift (rho := w) hlo f -
        (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)‖ := by
  let x := burnolMellinDividedShift (rho := w) hlo f -
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)
  have hbase := burnolMellinDividedShift_sub_evaluationVector_sourceProjection_lower_bound
    hlo hhi hb hz hfS
  have hproj : ‖burnolCoPoissonSourceProjection b x‖ ≤ ‖x‖ := by
    letI : CompleteSpace (burnolCoPoissonSourceSpace b) :=
      (isClosed_burnolCoPoissonSourceSpace b).completeSpace_coe
    exact (burnolCoPoissonSourceSpace b).norm_starProjection_apply_le x
  exact hbase.trans (mul_le_mul_of_nonneg_left hproj (norm_nonneg f))

/-- No nonzero co-Poisson source vector can have its divided shift equal a zero evaluation
vector. -/
theorem burnolMellinDividedShift_ne_evaluationVector_of_riemannZeta_eq_zero
    {w : ℂ} {b : ℝ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) (hb : 0 < b)
    (hz : riemannZeta w = 0) {f : evenSubspace}
    (hfS : f ∈ burnolCoPoissonSourceSpace b) (hf : f ≠ 0) :
    burnolMellinDividedShift (rho := w) hlo f ≠
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace) := by
  intro heq
  have hnot := burnolMellinDividedShift_not_mem_source_orthogonal hlo b hfS hf
  apply hnot
  rw [heq]
  exact burnolExtendedSoninEvaluationVector_mem_source_orthogonal hlo hhi hb
    (burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero hlo hhi hb hz)

end RHTower
