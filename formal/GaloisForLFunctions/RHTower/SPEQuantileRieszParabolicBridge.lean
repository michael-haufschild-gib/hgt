import GaloisForLFunctions.RHTower.SPEQuantileRieszSourceTransport
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantilePolarParabolicCompletedSourceBoundary

/-!
# SP-E Riesz transport as a terminal-completed parabolic carrier

The source-forced SP-E Riesz current has two exact components once the literal prime--polar
cells are compared with their equal-mass matched cells.  The local difference is the matched
quadrature defect.  The remaining finite source is the Riesz readout of the parabolic
matched-minus-completed-quantile codiagonal.  This module proves that decomposition without
discarding the terminal interval, the two degenerate initial cells, or the lower-edge correction.

The result is a bridge, not an RH estimate: cofinal control of the retained completed parabolic
readout and the normalized matched-defect term is still required.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The order-one Riesz test evaluated on the two nonconstant coordinates of a parabolic
moment carrier. -/
def speQuantileRieszParabolicReadout (M : ℕ) (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (M : ℝ) * v 1 - v 2

/-- The parabolic Riesz readout of one oriented mass interval is its exact Riesz primitive
difference. -/
theorem speQuantileRieszParabolicReadout_moment (M : ℕ) (a b : ℝ) :
    speQuantileRieszParabolicReadout M (ccmParabolicMoment a b) =
      speQuantileRieszMassAntiderivative M b -
        speQuantileRieszMassAntiderivative M a := by
  simp [speQuantileRieszParabolicReadout, ccmParabolicMoment,
    speQuantileRieszMassAntiderivative]
  ring

/-- Polar-coordinate primitive identity for the SP-E Riesz profile on every oriented height
interval. -/
theorem speQuantileRieszIntervalIntegral_eq_massAntiderivative
    (M : ℕ) (lo hi : ℝ) :
    (∫ h in lo..hi, Real.exp (h / 2) * speQuantileRieszProfile M h) =
      speQuantileRieszMassAntiderivative M (ccmActualHeadPolarMassCoordinate hi) -
        speQuantileRieszMassAntiderivative M (ccmActualHeadPolarMassCoordinate lo) := by
  let P : ℝ → ℝ := fun h =>
    2 * Real.sqrt (M : ℝ) * Real.exp h -
      (4 / 3 : ℝ) * Real.exp (h * 3 / 2)
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * speQuantileRieszProfile M h
  have hderiv : ∀ h ∈ uIcc lo hi, HasDerivAt P (G h) h := by
    intro h hh
    have hlin : HasDerivAt (fun x : ℝ => x * 3 / 2) (3 / 2 : ℝ) h := by
      simpa [mul_comm] using ((hasDerivAt_id h).const_mul (3 : ℝ)).div_const (2 : ℝ)
    have hthree : HasDerivAt (fun x : ℝ => Real.exp (x * 3 / 2))
        ((3 / 2 : ℝ) * Real.exp (h * 3 / 2)) h := by
      simpa [mul_comm] using hlin.exp
    have hraw :=
      ((Real.hasDerivAt_exp h).const_mul (2 * Real.sqrt (M : ℝ))).sub
        (hthree.const_mul (4 / 3 : ℝ))
    change HasDerivAt P (G h) h
    dsimp only [P, G, speQuantileRieszProfile]
    rw [show h * 3 / 2 = h + h / 2 by ring, Real.exp_add] at hraw
    apply HasDerivAt.congr_deriv hraw
    have hsquareexp : Real.exp (h / 2) ^ (2 : ℕ) = Real.exp h := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      2 * Real.sqrt (M : ℝ) * Real.exp h -
          (4 / 3 : ℝ) * ((3 / 2 : ℝ) *
            (Real.exp h * Real.exp (h / 2))) =
          2 * Real.sqrt (M : ℝ) * Real.exp h -
            2 * Real.exp h * Real.exp (h / 2) := by ring
      _ = 2 * Real.sqrt (M : ℝ) * Real.exp (h / 2) ^ (2 : ℕ) -
            2 * Real.exp h * Real.exp (h / 2) := by rw [hsquareexp]
      _ = Real.exp (h / 2) *
          (2 * (Real.sqrt (M : ℝ) * Real.exp (h / 2) - Real.exp h)) := by ring
  have hint : IntervalIntegrable G volume lo hi := by
    dsimp only [G]
    exact ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (continuous_speQuantileRieszProfile M)).intervalIntegrable _ _
  have hprimitive :
      (∫ h in lo..hi, Real.exp (h / 2) * speQuantileRieszProfile M h) =
        P hi - P lo := by
    rw [show (fun h : ℝ => Real.exp (h / 2) * speQuantileRieszProfile M h) = G by rfl]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hP (h : ℝ) :
      P h = speQuantileRieszMassAntiderivative M (ccmActualHeadPolarMassCoordinate h) := by
    dsimp only [P, speQuantileRieszMassAntiderivative, ccmActualHeadPolarMassCoordinate]
    have hsq : Real.exp (h / 2) ^ (2 : ℕ) = Real.exp h := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hcub : Real.exp (h / 2) ^ (3 : ℕ) = Real.exp (h * 3 / 2) := by
      rw [pow_three, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← hsq, ← hcub]
    ring
  rw [hprimitive, hP, hP]

/-- The Riesz readout of one literal matched parabolic moment is its original weighted height
integral. -/
theorem speQuantileRieszParabolicReadout_matchedMoment
    (M n : ℕ) :
    speQuantileRieszParabolicReadout M (ccmActualHeadMatchedParabolicMoment n) =
      ∫ h in (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)..
        (Real.log n + ccmActualHeadMatchedPrimePolarRadius n),
        Real.exp (h / 2) * speQuantileRieszProfile M h := by
  rw [ccmActualHeadMatchedParabolicMoment,
    speQuantileRieszParabolicReadout_moment]
  symm
  simpa only [ccmActualHeadMatchedPolarLowerCoordinate,
    ccmActualHeadMatchedPolarUpperCoordinate, ccmActualHeadPolarMassCoordinate] using
    speQuantileRieszIntervalIntegral_eq_massAntiderivative M
      (Real.log n - ccmActualHeadMatchedPrimePolarRadius n)
      (Real.log n + ccmActualHeadMatchedPrimePolarRadius n)

/-- The Riesz readout of one literal quantile parabolic moment is its original weighted height
integral. -/
theorem speQuantileRieszParabolicReadout_quantileMoment
    (M n : ℕ) :
    speQuantileRieszParabolicReadout M (ccmActualHeadQuantileParabolicMoment n) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
        Real.exp (h / 2) * speQuantileRieszProfile M h := by
  rw [ccmActualHeadQuantileParabolicMoment,
    speQuantileRieszParabolicReadout_moment]
  symm
  exact speQuantileRieszCellIntegral_eq_massAntiderivative M n

/-- The finite parabolic codiagonal is exactly the matched-minus-quantile Riesz integral on the
literal head. -/
theorem speQuantileRieszParabolicReadout_codiagonal
    (M K : ℕ) :
    speQuantileRieszParabolicReadout M
        (ccmActualHeadMatchedQuantileParabolicCodiagonal K) =
      (∑ n ∈ Finset.range (K + 1),
        ∫ h in (Real.log (n + 2) - ccmActualHeadMatchedPrimePolarRadius (n + 2))..
          (Real.log (n + 2) + ccmActualHeadMatchedPrimePolarRadius (n + 2)),
          Real.exp (h / 2) * speQuantileRieszProfile M h) -
        ∑ n ∈ Finset.range (K + 1),
          ∫ h in ccmOutgoingPrimeQuantileBoundary (n + 2)..
            ccmOutgoingPrimeQuantileBoundary (n + 3),
            Real.exp (h / 2) * speQuantileRieszProfile M h := by
  calc
    speQuantileRieszParabolicReadout M
        (ccmActualHeadMatchedQuantileParabolicCodiagonal K) =
        ∑ n ∈ Finset.range (K + 1),
          (speQuantileRieszParabolicReadout M
              (ccmActualHeadMatchedParabolicMoment (n + 2)) -
            speQuantileRieszParabolicReadout M
              (ccmActualHeadQuantileParabolicMoment (n + 2))) := by
          unfold ccmActualHeadMatchedQuantileParabolicCodiagonal
            speQuantileRieszParabolicReadout
          simp only [Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib]
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
          ring
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp_rw [speQuantileRieszParabolicReadout_matchedMoment,
        speQuantileRieszParabolicReadout_quantileMoment]
      norm_num [Nat.cast_add]

/-- Equivalent algebraic form of the finite codiagonal readout. -/
theorem speQuantileRieszParabolicReadout_codiagonal_eq_sum_difference
    (M K : ℕ) :
    speQuantileRieszParabolicReadout M
        (ccmActualHeadMatchedQuantileParabolicCodiagonal K) =
      (∑ n ∈ Finset.range (K + 1),
        speQuantileRieszParabolicReadout M
          (ccmActualHeadMatchedParabolicMoment (n + 2))) -
        ∑ n ∈ Finset.range (K + 1),
          speQuantileRieszParabolicReadout M
            (ccmActualHeadQuantileParabolicMoment (n + 2)) := by
  unfold ccmActualHeadMatchedQuantileParabolicCodiagonal
    speQuantileRieszParabolicReadout
  simp only [Finset.sum_apply, Pi.sub_apply]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  ring

/-- The literal terminal Riesz integral is the Riesz readout of its terminal parabolic moment. -/
theorem speQuantileRieszParabolicReadout_terminal
    (M K : ℕ) :
    speQuantileRieszParabolicReadout M
        (ccmActualHeadQuantileParabolicTerminal K (Real.log M)) =
      ∫ h in ccmOutgoingPrimeQuantileBoundary (K + 3)..Real.log M,
        Real.exp (h / 2) * speQuantileRieszProfile M h := by
  rw [ccmActualHeadQuantileParabolicTerminal,
    speQuantileRieszParabolicReadout_moment]
  symm
  simpa only [ccmActualHeadQuantilePolarCoordinate,
    ccmActualHeadPolarMassCoordinate] using
    speQuantileRieszIntervalIntegral_eq_massAntiderivative M
      (ccmOutgoingPrimeQuantileBoundary (K + 3)) (Real.log M)

/-- At its physical wall, the literal terminal reporter is the negative terminal parabolic
Riesz readout. -/
theorem speQuantileRieszTerminal_eq_neg_parabolicReadout
    {M K : ℕ} (hM : 0 < M) :
    ccmPrimePolarReporterQuantileTerminalTransport
        (speQuantileRieszProfile M) (K + 3) (Real.log M) =
      -speQuantileRieszParabolicReadout M
        (ccmActualHeadQuantileParabolicTerminal K (Real.log M)) := by
  rw [ccmPrimePolarReporterQuantileTerminalTransport,
    speQuantileRieszProfile_log_eq_zero hM]
  calc
    (∫ h in ccmOutgoingPrimeQuantileBoundary (K + 3)..Real.log M,
        Real.exp (h / 2) * (0 - speQuantileRieszProfile M h)) =
      -(∫ h in ccmOutgoingPrimeQuantileBoundary (K + 3)..Real.log M,
        Real.exp (h / 2) * speQuantileRieszProfile M h) := by
          rw [← intervalIntegral.integral_neg]
          apply intervalIntegral.integral_congr
          intro h hh
          ring
    _ = _ := by rw [← speQuantileRieszParabolicReadout_terminal]

private theorem speQuantileRiesz_quantileBoundary_one :
    ccmOutgoingPrimeQuantileBoundary 1 = 0 := by
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  simp [ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative, hzero]

private theorem speQuantileRiesz_quantileBoundary_two :
    ccmOutgoingPrimeQuantileBoundary 2 = 0 := by
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    simp [criticalMellinAtomWeight]
  have hone : criticalMellinAtomWeight 1 = 0 := by
    simp [criticalMellinAtomWeight]
  simp [ccmOutgoingPrimeQuantileBoundary, ccmOutgoingPrimeCumulative,
    Finset.sum_range_succ, hzero, hone]

private theorem speQuantileRieszReporterCell_zero (M : ℕ) :
    ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) 0 = 0 := by
  simp [ccmPrimePolarReporterQuantileCellTransport,
    ccmOutgoingPrimeQuantileBoundary_zero,
    speQuantileRiesz_quantileBoundary_one]

private theorem speQuantileRieszReporterCell_one (M : ℕ) :
    ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) 1 = 0 := by
  simp [ccmPrimePolarReporterQuantileCellTransport,
    speQuantileRiesz_quantileBoundary_one,
    speQuantileRiesz_quantileBoundary_two]

/-- One literal SP-E reporter cell is its matched local quadrature defect plus the exact
parabolic matched-minus-quantile Riesz displacement. -/
theorem speQuantileRieszReporterCell_eq_matchedQuadratureDefect_add_parabolicDifference
    (M n : ℕ) :
    ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n =
      ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) n +
        (speQuantileRieszParabolicReadout M (ccmActualHeadMatchedParabolicMoment n) -
          speQuantileRieszParabolicReadout M (ccmActualHeadQuantileParabolicMoment n)) := by
  rw [← speQuantileRieszAtom_sub_cellIntegral_eq_reporterTransport]
  unfold ccmMatchedPrimePolarQuadratureDefect
  rw [← speQuantileRieszParabolicReadout_matchedMoment,
    ← speQuantileRieszParabolicReadout_quantileMoment]
  ring

/-- Summed literal SP-E head equals matched quadrature defect plus finite parabolic readout. -/
theorem sum_speQuantileRieszReporterCells_shift_two_eq_matchedQuadratureDefect_add_parabolic
    (M K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
      ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) (n + 2)) =
      (∑ n ∈ Finset.range (K + 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) +
        speQuantileRieszParabolicReadout M
          (ccmActualHeadMatchedQuantileParabolicCodiagonal K) := by
  calc
    (∑ n ∈ Finset.range (K + 1),
      ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) (n + 2)) =
        ∑ n ∈ Finset.range (K + 1),
          (ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2) +
            (speQuantileRieszParabolicReadout M
                (ccmActualHeadMatchedParabolicMoment (n + 2)) -
              speQuantileRieszParabolicReadout M
                (ccmActualHeadQuantileParabolicMoment (n + 2)))) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact speQuantileRieszReporterCell_eq_matchedQuadratureDefect_add_parabolicDifference
            M (n + 2)
    _ = (∑ n ∈ Finset.range (K + 1),
          ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) +
        speQuantileRieszParabolicReadout M
          (ccmActualHeadMatchedQuantileParabolicCodiagonal K) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            speQuantileRieszParabolicReadout_codiagonal_eq_sum_difference]

/-- Terminal completion of the codiagonal is exactly terminal completion of the Riesz readout. -/
theorem speQuantileRieszParabolicReadout_completedCodiagonal
    (M K : ℕ) (T : ℝ) :
    speQuantileRieszParabolicReadout M
        (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal K T) =
      speQuantileRieszParabolicReadout M
        (ccmActualHeadMatchedQuantileParabolicCodiagonal K) -
      speQuantileRieszParabolicReadout M
        (ccmActualHeadQuantileParabolicTerminal K T) := by
  unfold ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal
    ccmActualHeadCompletedQuantileParabolicAggregate
    ccmActualHeadMatchedQuantileParabolicCodiagonal
    ccmActualHeadMatchedParabolicAggregate
    ccmActualHeadQuantileParabolicAggregate
    speQuantileRieszParabolicReadout
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.add_apply]
  ring

private theorem sum_speQuantileRieszReporterCells_range_eq_shift_two
    {M : ℕ} (hM : 3 ≤ M) :
    (∑ n ∈ Finset.range M,
      ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n) =
      ∑ n ∈ Finset.range ((M - 3) + 1),
        ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) (n + 2) := by
  have hrange : Finset.range M =
      insert 0 (insert 1 (Finset.Icc 2 (M - 1))) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzero : 0 ∉ insert 1 (Finset.Icc 2 (M - 1)) := by simp
  have hone : 1 ∉ Finset.Icc 2 (M - 1) := by simp
  have hupper : (M - 3) + 2 = M - 1 := by omega
  calc
    (∑ n ∈ Finset.range M,
      ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n) =
        ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) 0 +
          ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) 1 +
          ∑ n ∈ Finset.Icc 2 (M - 1),
            ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n := by
          rw [hrange, Finset.sum_insert hzero, Finset.sum_insert hone]
          ring
    _ = ∑ n ∈ Finset.Icc 2 (M - 1),
          ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n := by
          rw [speQuantileRieszReporterCell_zero,
            speQuantileRieszReporterCell_one]
          ring
    _ = ∑ n ∈ Finset.range ((M - 3) + 1),
          ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) (n + 2) := by
          symm
          simpa only [hupper] using
            (sum_range_shift_two_eq_sum_Icc_two (M - 3)
              (fun n => ccmPrimePolarReporterQuantileCellTransport
                (speQuantileRieszProfile M) n))

/-- **Completed SP-E--parabolic bridge.** For every nondegenerate integer aperture, the literal
completed SP-E Riesz transport is exactly its matched quadrature defect plus the Riesz readout of
the terminal-completed parabolic codiagonal, with the forced lower correction retained. -/
theorem speCompletedQuantileRieszTransport_eq_matchedQuadratureDefect_add_completedParabolic
    {M : ℕ} (hM : 3 ≤ M) :
    speCompletedQuantileRieszTransport M =
      (∑ n ∈ Finset.range ((M - 3) + 1),
        ccmMatchedPrimePolarQuadratureDefect (speQuantileRieszProfile M) (n + 2)) +
        speQuantileRieszParabolicReadout M
          (ccmActualHeadMatchedCompletedQuantileParabolicCodiagonal (M - 3) (Real.log M)) -
        2 * (Real.sqrt M - 2 / 3) := by
  have hMpos : 0 < M := by omega
  have hindex : (M - 3) + 3 = M := by omega
  unfold speCompletedQuantileRieszTransport
    ccmPrimePolarReporterCompletedQuantileTransport
  calc
    (∑ n ∈ Finset.range M,
      ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n) +
        ccmPrimePolarReporterQuantileTerminalTransport
          (speQuantileRieszProfile M) M (Real.log M) -
        2 * (Real.sqrt M - 2 / 3) =
      (∑ n ∈ Finset.range ((M - 3) + 1),
        ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) (n + 2)) +
        ccmPrimePolarReporterQuantileTerminalTransport
          (speQuantileRieszProfile M) ((M - 3) + 3) (Real.log M) -
        2 * (Real.sqrt M - 2 / 3) := by
          rw [sum_speQuantileRieszReporterCells_range_eq_shift_two hM, hindex]
    _ = _ := by
      rw [sum_speQuantileRieszReporterCells_shift_two_eq_matchedQuadratureDefect_add_parabolic,
        speQuantileRieszTerminal_eq_neg_parabolicReadout hMpos,
        speQuantileRieszParabolicReadout_completedCodiagonal]
      ring

end RHTower
