import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal

/-!
# Literal adjacent-codiagonal source bridge

Above the first nonempty physical prime head, the matched polar coverage seam is exactly its
oriented adjacent mass-coordinate codiagonal minus the one remaining physical terminal interval.
This keeps the matched prime cells, equal-mass quantile cells, and terminal orientation in a
single signed source identity.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

private theorem sum_ccmActualHeadQuantilePolarCells_eq_interval
    (K : ℕ) (f : SoninL2) :
    (∑ n ∈ Finset.range (K + 1),
      ∫ y in ccmActualHeadQuantilePolarCoordinate (n + 2)..
          ccmActualHeadQuantilePolarCoordinate (n + 3),
        ccmActualHeadPolarMassDefectProfile f y) =
      ∫ y in ccmActualHeadQuantilePolarCoordinate 2..
          ccmActualHeadQuantilePolarCoordinate (K + 3),
        ccmActualHeadPolarMassDefectProfile f y := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hleft : IntervalIntegrable (ccmActualHeadPolarMassDefectProfile f) volume
          (ccmActualHeadQuantilePolarCoordinate 2)
          (ccmActualHeadQuantilePolarCoordinate (K + 3)) :=
        ccmActualHeadPolarMassDefectProfile_intervalIntegrable_of_pos f
          (by unfold ccmActualHeadQuantilePolarCoordinate; positivity)
          (by unfold ccmActualHeadQuantilePolarCoordinate; positivity)
      have hright : IntervalIntegrable (ccmActualHeadPolarMassDefectProfile f) volume
          (ccmActualHeadQuantilePolarCoordinate (K + 3))
          (ccmActualHeadQuantilePolarCoordinate (K + 4)) :=
        ccmActualHeadPolarMassDefectProfile_intervalIntegrable_of_pos f
          (by unfold ccmActualHeadQuantilePolarCoordinate; positivity)
          (by unfold ccmActualHeadQuantilePolarCoordinate; positivity)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        intervalIntegral.integral_add_adjacent_intervals hleft hright

/-- **Source-faithful adjacent-seam law.** Once the physical cutoff contains the integer head
`2, ..., M`, the entire matched coverage seam is its signed adjacent codiagonal, less exactly the
one oriented interval from the terminal quantile boundary to the physical Gamma height.  This is
an equality; no absolute-value or positivity estimate is taken. -/
theorem ccmActualHeadMatchedPolarCoverageSeam_eq_adjacentCodiagonal_sub_terminal
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a)
    (hcutoff : 2 ≤ Nat.floor (Real.exp (2 * a.1))) :
    let M := Nat.floor (Real.exp (2 * a.1))
    ccmActualHeadMatchedPolarCoverageSeam a f =
      ccmActualHeadMatchedPolarAdjacentCodiagonal (M - 2) f.1 -
        ∫ h in ccmOutgoingPrimeQuantileBoundary (M + 1)..(2 * a.1),
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1 := by
  let M := Nat.floor (Real.exp (2 * a.1))
  have hseam := ccmActualHeadMatchedPolarCoverageSeam_eq_rigidCellTransports_sub_terminal a f
  change 2 ≤ M at hcutoff
  change ccmActualHeadMatchedPolarCoverageSeam a f =
    (∑ n ∈ Finset.Icc 2 M,
      ((∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
            ccmActualHeadMatchedPolarUpperCoordinate n,
          ccmActualHeadPolarMassDefectProfile f.1 y) -
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
            ccmActualHeadMatchedPolarUpperCoordinate n,
          ccmActualHeadPolarMassDefectProfile f.1
            (ccmActualHeadMatchedQuantilePolarDisplacement n + y))) -
      ∫ h in ccmOutgoingPrimeQuantileBoundary (M + 1)..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1 at hseam
  change ccmActualHeadMatchedPolarCoverageSeam a f =
    ccmActualHeadMatchedPolarAdjacentCodiagonal (M - 2) f.1 -
      ∫ h in ccmOutgoingPrimeQuantileBoundary (M + 1)..(2 * a.1),
        Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1
  rw [hseam]
  congr 1
  rw [ccmActualHeadMatchedPolarAdjacentCodiagonal_eq_IccCells_sub_quantile]
  have hindex₁ : M - 2 + 2 = M := by omega
  have hindex₂ : M - 2 + 3 = M + 1 := by omega
  rw [hindex₁, hindex₂]
  have hquantile :
      (∑ n ∈ Finset.Icc 2 M,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
            ccmActualHeadMatchedPolarUpperCoordinate n,
          ccmActualHeadPolarMassDefectProfile f.1
            (ccmActualHeadMatchedQuantilePolarDisplacement n + y)) =
        ∫ y in ccmActualHeadQuantilePolarCoordinate 2..
            ccmActualHeadQuantilePolarCoordinate (M + 1),
          ccmActualHeadPolarMassDefectProfile f.1 y := by
    calc
      (∑ n ∈ Finset.Icc 2 M,
        ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
            ccmActualHeadMatchedPolarUpperCoordinate n,
          ccmActualHeadPolarMassDefectProfile f.1
            (ccmActualHeadMatchedQuantilePolarDisplacement n + y)) =
          ∑ n ∈ Finset.range (M - 2 + 1),
            ∫ y in ccmActualHeadMatchedPolarLowerCoordinate (n + 2)..
                ccmActualHeadMatchedPolarUpperCoordinate (n + 2),
              ccmActualHeadPolarMassDefectProfile f.1
                (ccmActualHeadMatchedQuantilePolarDisplacement (n + 2) + y) := by
          simpa only [hindex₁] using
            (sum_range_shift_two_eq_sum_Icc_two (M - 2)
              (fun n => ∫ y in ccmActualHeadMatchedPolarLowerCoordinate n..
                ccmActualHeadMatchedPolarUpperCoordinate n,
                ccmActualHeadPolarMassDefectProfile f.1
                  (ccmActualHeadMatchedQuantilePolarDisplacement n + y))).symm
      _ = ∑ n ∈ Finset.range (M - 2 + 1),
          ∫ y in ccmActualHeadQuantilePolarCoordinate (n + 2)..
              ccmActualHeadQuantilePolarCoordinate (n + 3),
            ccmActualHeadPolarMassDefectProfile f.1 y := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [← ccmActualHeadOutgoingQuantilePolarCell_eq_matchedCoordinateTranslate,
            ccmActualHeadOutgoingQuantilePolarCell_eq_polarMassCoordinate]
      _ = ∫ y in ccmActualHeadQuantilePolarCoordinate 2..
          ccmActualHeadQuantilePolarCoordinate (M - 2 + 3),
          ccmActualHeadPolarMassDefectProfile f.1 y :=
        sum_ccmActualHeadQuantilePolarCells_eq_interval (M - 2) f.1
      _ = _ := by rw [hindex₂]
  rw [← hquantile, ← Finset.sum_sub_distrib]

/-- **Actual-head signed normal form.** The restricted Weil source is positive Gamma data and
the literal matched symmetric-minus-Suzuki block, followed by the signed adjacent codiagonal and
its oriented terminal interval.  Consequently, a lower bound must act on this joint source; no
coverage scalar has been dropped. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_matchedSignedAdjacentCodiagonal_sub_terminal
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hcutoff : 2 ≤ Nat.floor (Real.exp (2 * a.1))) :
    let f := ccmArchimedeanFormToAperture a u
    let M := Nat.floor (Real.exp (2 * a.1))
    let F := Finset.Icc 2 M
    ccmRestrictedWeilSourceQuadratic a u =
      2 * gammaHardyPhaseRate 0 * ‖f‖ ^ 2 +
        ccmActualHeadGammaHigherBinetModeEnergy (f : SoninL2) +
        (2 * Real.exp a.1 - criticalMellinPrimeMass (2 * a.1)) *
          ccmActualHeadTranslationDefect (2 * a.1) f.1 +
        ccmActualHeadMatchedSymmetricFiniteBlock F f.1 -
        ccmActualHeadMatchedSuzukiFiniteBlock F f.1 +
        ccmActualHeadMatchedPolarAdjacentCodiagonal (M - 2) f.1 -
        ∫ h in ccmOutgoingPrimeQuantileBoundary (M + 1)..(2 * a.1),
          Real.exp (h / 2) * ccmActualHeadTranslationDefect h f.1 := by
  dsimp only
  rw [ccmRestrictedWeilSourceQuadratic_eq_matchedSymmetric_sub_suzuki_add_coverageSeam,
    ccmActualHeadMatchedPolarCoverageSeam_eq_adjacentCodiagonal_sub_terminal a
      (ccmArchimedeanFormToAperture a u) hcutoff]
  ring

end RHTower
