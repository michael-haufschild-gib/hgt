import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCompletedQuantileTransport

/-!
# Discrete derivative of completed third-grade quantile transport

The completed quantile transport is the literal finite prime--polar source, including its
terminal seam.  Advancing its quantile index causes the two polar cell integrals to cancel
exactly.  The surviving increment is one critical Mellin atom tested against its displacement
from the fixed terminal reporter value.  This isolates the arithmetic object that a moving-wall
estimate must control without separating prime and polar contributions prematurely.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Advancing the quantile index cancels the full polar cell exactly, leaving only the literal
prime atom evaluated against terminal displacement. -/
theorem ccmPrimePolarReporterCompletedQuantileTransport_succ_sub
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) (T : ℝ) :
    ccmPrimePolarReporterCompletedQuantileTransport F (N + 1) T -
        ccmPrimePolarReporterCompletedQuantileTransport F N T =
      criticalMellinAtomWeight N * (F (Real.log N) - F T) := by
  let lo := ccmOutgoingPrimeQuantileBoundary N
  let hi := ccmOutgoingPrimeQuantileBoundary (N + 1)
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * (F T - F h)
  have hG : Continuous G :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (continuous_const.sub hF)
  have hterminal :
      ccmPrimePolarReporterQuantileTerminalTransport F N T =
        (∫ h in lo..hi, G h) +
          ccmPrimePolarReporterQuantileTerminalTransport F (N + 1) T := by
    change (∫ h in lo..T, G h) = (∫ h in lo..hi, G h) + ∫ h in hi..T, G h
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hG.intervalIntegrable (μ := volume) lo hi)
      (hG.intervalIntegrable (μ := volume) hi T)).symm
  have hcellIntegrable : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * (F (Real.log N) - F h)) volume lo hi :=
    ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (continuous_const.sub hF)).intervalIntegrable _ _
  have hterminalCellIntegrable : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * (F T - F h)) volume lo hi :=
    hG.intervalIntegrable _ _
  have hcell :
      ccmPrimePolarReporterQuantileCellTransport F N - ∫ h in lo..hi, G h =
        criticalMellinAtomWeight N * (F (Real.log N) - F T) := by
    rw [ccmPrimePolarReporterQuantileCellTransport]
    calc
      (∫ h in lo..hi, Real.exp (h / 2) * (F (Real.log N) - F h)) -
          ∫ h in lo..hi, G h =
        ∫ h in lo..hi,
          (Real.exp (h / 2) * (F (Real.log N) - F h) - G h) :=
          (intervalIntegral.integral_sub hcellIntegrable hterminalCellIntegrable).symm
      _ = ∫ h in lo..hi,
          Real.exp (h / 2) * (F (Real.log N) - F T) := by
          apply intervalIntegral.integral_congr
          intro h hh
          dsimp only [G]
          ring
      _ = (F (Real.log N) - F T) * ∫ h in lo..hi, Real.exp (h / 2) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro h hh
          ring
      _ = _ := by
          rw [integral_exp_half_quantileCell_eq_atomWeight]
          ring
  rw [ccmPrimePolarReporterCompletedQuantileTransport,
    ccmPrimePolarReporterCompletedQuantileTransport,
    Finset.sum_range_succ, hterminal]
  linarith

/-- For the literal clipped third-grade reporter, a fixed-wall quantile advance is exactly one
critical atom times its reporter value: the terminal value vanishes at the physical wall. -/
theorem ccmThirdGradeCesaroQuantileTransport_fixedWall_succ_sub
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (N : ℕ) :
    ccmPrimePolarReporterCompletedQuantileTransport
        (ccmThirdGradeCesaroClippedTriangularWeight b H) (N + 1) H -
      ccmPrimePolarReporterCompletedQuantileTransport
        (ccmThirdGradeCesaroClippedTriangularWeight b H) N H =
      criticalMellinAtomWeight N *
        ccmThirdGradeCesaroClippedTriangularWeight b H (Real.log N) := by
  rw [ccmPrimePolarReporterCompletedQuantileTransport_succ_sub _
    (lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight hb hbH).continuous,
    ccmThirdGradeCesaroClippedTriangularWeight_endpoint hb hbH]
  ring

/-- Every fixed-wall quantile-index increment of the literal completed transport is nonnegative.
Thus the required CCM-FU cancellation cannot occur among added quantile cells; it must remain
coupled to the terminal polar baseline. -/
theorem ccmThirdGradeCesaroQuantileTransport_fixedWall_succ_sub_nonneg
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (N : ℕ) :
    0 ≤ ccmPrimePolarReporterCompletedQuantileTransport
        (ccmThirdGradeCesaroClippedTriangularWeight b H) (N + 1) H -
      ccmPrimePolarReporterCompletedQuantileTransport
        (ccmThirdGradeCesaroClippedTriangularWeight b H) N H := by
  rw [ccmThirdGradeCesaroQuantileTransport_fixedWall_succ_sub hb hbH]
  exact mul_nonneg (criticalMellinAtomWeight_nonneg_cCMActualHeadWallGramSignedProducer _) (le_max_right _ _)

/-- On a common wall interval, the entire continuous deformation of the literal triangular
reporter is its exact reciprocal-wall drift.  This is the second coordinate, alongside quantile
index advances, in a source-faithful moving-boundary analysis. -/
theorem ccmGuinandWeilThirdGradeCesaroTriangularWeight_wall_sub
    {H K h : ℝ} (hH : H ≠ 0) (hK : K ≠ 0) :
    ccmGuinandWeilThirdGradeCesaroTriangularWeight H h -
        ccmGuinandWeilThirdGradeCesaroTriangularWeight K h =
      ccmGuinandWeilThirdGradeWeight h * h * (1 / K - 1 / H) := by
  unfold ccmGuinandWeilThirdGradeCesaroTriangularWeight
  field_simp
  ring

end GaloisForLFunctions.RHTower
