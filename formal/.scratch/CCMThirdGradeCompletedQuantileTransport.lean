import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeMatchedQuadrature
import GaloisForLFunctions.RHTower.CCMActualHeadOutgoingQuantileTransportProducer

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- One exact prime-quantile reporter transport cell. -/
def ccmPrimePolarReporterQuantileCellTransport
    (F : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary n..
      ccmOutgoingPrimeQuantileBoundary (n + 1),
    Real.exp (h / 2) * (F (Real.log n) - F h)

/-- Oriented terminal reporter transport from the last quantile boundary to the physical wall. -/
def ccmPrimePolarReporterQuantileTerminalTransport
    (F : ℝ → ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  ∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
    Real.exp (h / 2) * (F T - F h)

/-- Cells and terminal seam are added before any absolute value or energy square. -/
def ccmPrimePolarReporterCompletedQuantileTransport
    (F : ℝ → ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N,
      ccmPrimePolarReporterQuantileCellTransport F n) +
    ccmPrimePolarReporterQuantileTerminalTransport F N T

private theorem primeAtom_sub_quantileCell_eq_reporterTransport
    (F : ℝ → ℝ) (hF : Continuous F) (n : ℕ) :
    criticalMellinAtomWeight n * F (Real.log n) -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
            ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * F h) =
      ccmPrimePolarReporterQuantileCellTransport F n := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  have hweight : Continuous (fun h : ℝ => Real.exp (h / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F (Real.log n)) volume lo hi :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F h) volume lo hi :=
    (hweight.mul hF).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  have hfirst :
      (∫ h in lo..hi, Real.exp (h / 2) * F (Real.log n)) =
        criticalMellinAtomWeight n * F (Real.log n) := by
    calc
      _ = F (Real.log n) * ∫ h in lo..hi, Real.exp (h / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
      _ = _ := by rw [hmass]; ring
  rw [ccmPrimePolarReporterQuantileCellTransport]
  calc
    criticalMellinAtomWeight n * F (Real.log n) -
        (∫ h in lo..hi, Real.exp (h / 2) * F h) =
      (∫ h in lo..hi, Real.exp (h / 2) * F (Real.log n)) -
        ∫ h in lo..hi, Real.exp (h / 2) * F h := by rw [hfirst]
    _ = ∫ h in lo..hi,
        (Real.exp (h / 2) * F (Real.log n) -
          Real.exp (h / 2) * F h) :=
      (intervalIntegral.integral_sub hconst hvar).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring

private theorem sum_reporterQuantileCells_eq_prime_sub_polar
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) :
    (∑ n ∈ Finset.range N,
        ccmPrimePolarReporterQuantileCellTransport F n) =
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n * F (Real.log n)) -
        ∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * F h := by
  have hpartition :
      (∫ h in (0 : ℝ)..ccmOutgoingPrimeQuantileBoundary N,
          Real.exp (h / 2) * F h) =
        ∑ n ∈ Finset.range N,
          ∫ h in ccmOutgoingPrimeQuantileBoundary n..
              ccmOutgoingPrimeQuantileBoundary (n + 1),
            Real.exp (h / 2) * F h := by
    let G : ℝ → ℝ := fun h => Real.exp (h / 2) * F h
    have hG : Continuous G :=
      (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul hF
    induction N with
    | zero => simp [ccmOutgoingPrimeQuantileBoundary_zero]
    | succ N ih =>
        rw [Finset.sum_range_succ, ← ih]
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hG.intervalIntegrable (μ := volume) 0
            (ccmOutgoingPrimeQuantileBoundary N))
          (hG.intervalIntegrable (μ := volume)
            (ccmOutgoingPrimeQuantileBoundary N)
            (ccmOutgoingPrimeQuantileBoundary (N + 1)))).symm
  rw [hpartition, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact (primeAtom_sub_quantileCell_eq_reporterTransport F hF n).symm

private theorem reporterTerminalTransport_eq_mass_sub_polar
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) (T : ℝ) :
    ccmPrimePolarReporterQuantileTerminalTransport F N T =
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2)) * F T -
      ∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2) * F h := by
  let lo := ccmOutgoingPrimeQuantileBoundary N
  have hweight : Continuous (fun h : ℝ => Real.exp (h / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F T) volume lo T :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * F h) volume lo T :=
    (hweight.mul hF).intervalIntegrable _ _
  rw [ccmPrimePolarReporterQuantileTerminalTransport]
  calc
    (∫ h in lo..T, Real.exp (h / 2) * (F T - F h)) =
      ∫ h in lo..T,
        (Real.exp (h / 2) * F T - Real.exp (h / 2) * F h) := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring
    _ = (∫ h in lo..T, Real.exp (h / 2) * F T) -
        ∫ h in lo..T, Real.exp (h / 2) * F h :=
      intervalIntegral.integral_sub hconst hvar
    _ = (∫ h in lo..T, Real.exp (h / 2)) * F T -
        ∫ h in lo..T, Real.exp (h / 2) * F h := by
      rw [intervalIntegral.integral_mul_const]

/-- Completed quantile transport equals the finite prime-minus-outgoing-polar reporter plus its
exact terminal mass coefficient. -/
theorem ccmPrimePolarReporterCompletedQuantileTransport_eq
    (F : ℝ → ℝ) (hF : Continuous F) (N : ℕ) (T : ℝ) :
    ccmPrimePolarReporterCompletedQuantileTransport F N T =
      (∑ n ∈ Finset.range N,
        criticalMellinAtomWeight n * F (Real.log n)) -
      (∫ h in (0 : ℝ)..T, Real.exp (h / 2) * F h) +
      (∫ h in ccmOutgoingPrimeQuantileBoundary N..T,
        Real.exp (h / 2)) * F T := by
  let lo := ccmOutgoingPrimeQuantileBoundary N
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * F h
  have hG : Continuous G :=
    (by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul hF
  have hsplit :
      (∫ h in (0 : ℝ)..T, G h) =
        (∫ h in (0 : ℝ)..lo, G h) + ∫ h in lo..T, G h :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hG.intervalIntegrable (μ := volume) 0 lo)
      (hG.intervalIntegrable (μ := volume) lo T)).symm
  dsimp only [G, lo] at hsplit
  rw [ccmPrimePolarReporterCompletedQuantileTransport,
    sum_reporterQuantileCells_eq_prime_sub_polar F hF N,
    reporterTerminalTransport_eq_mass_sub_polar F hF N T]
  linarith

/-- Actual third-grade reporter transported cellwise and through its oriented terminal seam. -/
def ccmThirdGradeCesaroCompletedQuantileTransport (b H : ℝ) : ℝ :=
  ccmPrimePolarReporterCompletedQuantileTransport
    (ccmThirdGradeCesaroClippedTriangularWeight b H)
    (Nat.floor (Real.exp H) + 1) H

theorem ccmThirdGradeCesaroClippedTriangularWeight_endpoint
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroClippedTriangularWeight b H H = 0 := by
  have hH : 0 < H := hb.trans_le hbH
  unfold ccmThirdGradeCesaroClippedTriangularWeight
  rw [max_eq_right hbH]
  simp [ccmGuinandWeilThirdGradeCesaroTriangularWeight,
    ccmGuinandWeilThirdGradeWeight, hH.ne']

/-- The terminal mass mismatch cancels exactly because the triangular reporter vanishes at the
moving wall. No terminal absolute bound is taken. -/
theorem ccmThirdGradeCesaroCompletedQuantileTransport_eq_fullOutgoing
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmThirdGradeCesaroCompletedQuantileTransport b H =
      (∑ n ∈ Finset.range (Nat.floor (Real.exp H) + 1),
        criticalMellinAtomWeight n *
          ccmThirdGradeCesaroClippedTriangularWeight b H (Real.log n)) -
      ∫ h in (0 : ℝ)..H,
        Real.exp (h / 2) * ccmThirdGradeCesaroClippedTriangularWeight b H h := by
  rw [ccmThirdGradeCesaroCompletedQuantileTransport,
    ccmPrimePolarReporterCompletedQuantileTransport_eq
      _ (lipschitzWith_ccmThirdGradeCesaroClippedTriangularWeight hb hbH).continuous]
  rw [ccmThirdGradeCesaroClippedTriangularWeight_endpoint hb hbH]
  ring

end GaloisForLFunctions.RHTower
