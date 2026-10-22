import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrunedBoundaryExcursionDefect
import GaloisForLFunctions.RHTower.PrimeGammaSignedEulerianCurvaturePluckerLift

/-!
# Four-label Pluecker survivor of literal Suzuki boundary excursions

The reflected `2,3` return legs through the distinct excluded prime vertices `7,11` form a
literal two-port source matrix.  Its first four-label minor is nonzero before any scalar
aggregation.  This is a source-carrier theorem only: no map to the completed outgoing current or
Route-P spectral readout is asserted here.
-/

open Complex Set ContinuousLinearMap

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

private def bFourPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def bFourPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩
private def bFourPrimeSeven : Nat.Primes := ⟨7, Nat.prime_seven⟩
private def bFourPrimeEleven : Nat.Primes := ⟨11, by norm_num⟩

private def bFourTwo : SuzukiSeamValuation := suzukiPrimePowerStep (bFourPrimeTwo, 1)
private def bFourThree : SuzukiSeamValuation := suzukiPrimePowerStep (bFourPrimeThree, 1)
private def bFourSeven : SuzukiSeamValuation := suzukiPrimePowerStep (bFourPrimeSeven, 1)
private def bFourEleven : SuzukiSeamValuation := suzukiPrimePowerStep (bFourPrimeEleven, 1)

private def bFourA : ℝ := Real.log 2
private def bFourSourceOne : SuzukiSeamVertex := (SuzukiSeamRoot.left, bFourSeven - bFourTwo)
private def bFourSourceTwo : SuzukiSeamVertex := (SuzukiSeamRoot.left, bFourEleven - bFourThree)
private def bFourReadoutThree : SuzukiSeamVertex := bFourSourceOne
private def bFourReadoutFour : SuzukiSeamVertex := bFourSourceTwo

private theorem coord_two : primeSeamCoordinate bFourTwo = Real.log 2 := by
  simp [bFourTwo, bFourPrimeTwo, primeSeamCoordinate_primePowerStep]

private theorem coord_three : primeSeamCoordinate bFourThree = Real.log 3 := by
  simp [bFourThree, bFourPrimeThree, primeSeamCoordinate_primePowerStep]

private theorem coord_seven : primeSeamCoordinate bFourSeven = Real.log 7 := by
  simp [bFourSeven, bFourPrimeSeven, primeSeamCoordinate_primePowerStep]

private theorem coord_eleven : primeSeamCoordinate bFourEleven = Real.log 11 := by
  simp [bFourEleven, bFourPrimeEleven, primeSeamCoordinate_primePowerStep]

private theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

private theorem log_two_lt_log_seven : Real.log 2 < Real.log 7 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem log_three_lt_log_eleven : Real.log 3 < Real.log 11 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem log_four_lt_log_seven : Real.log 4 < Real.log 7 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem log_four_lt_log_eleven : Real.log 4 < Real.log 11 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem log_seven_lt_log_eleven : Real.log 7 < Real.log 11 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

private theorem log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  calc
    Real.log 4 = Real.log (2 * 2) := by norm_num
    _ = Real.log 2 + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    _ = 2 * Real.log 2 := by ring

private theorem log_seven_lt_three_log_two : Real.log 7 < 3 * Real.log 2 := by
  have hlog : Real.log 7 < Real.log 8 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log (4 * 2) := by norm_num
      _ = Real.log 4 + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)]
        norm_num
      _ = Real.log (2 * 2) + Real.log 2 := by norm_num
      _ = Real.log 2 + Real.log 2 + Real.log 2 := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ = 3 * Real.log 2 := by ring
  linarith

private theorem log_eleven_lt_log_three_add_two_log_two :
    Real.log 11 < Real.log 3 + 2 * Real.log 2 := by
  have hlog : Real.log 11 < Real.log 12 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have h12 : Real.log 12 = Real.log 3 + 2 * Real.log 2 := by
    calc
      Real.log 12 = Real.log (3 * 4) := by norm_num
      _ = Real.log 3 + Real.log 4 := by
        rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
      _ = Real.log 3 + Real.log (2 * 2) := by norm_num
      _ = Real.log 3 + (Real.log 2 + Real.log 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
      _ = Real.log 3 + 2 * Real.log 2 := by ring
  linarith

private theorem source_one_admissible : bFourSourceOne ∈ suzukiAdmissibleSeamVertices bFourA := by
  rw [bFourSourceOne, suzukiAdmissibleSeamVertices_iff]
  simp only [map_sub, coord_seven, coord_two, bFourA]
  constructor <;> linarith [log_two_lt_log_seven, log_seven_lt_three_log_two]

private theorem source_two_admissible : bFourSourceTwo ∈ suzukiAdmissibleSeamVertices bFourA := by
  rw [bFourSourceTwo, suzukiAdmissibleSeamVertices_iff]
  simp only [map_sub, coord_eleven, coord_three, bFourA]
  constructor <;> linarith [log_three_lt_log_eleven, log_eleven_lt_log_three_add_two_log_two]

private theorem seven_not_admissible :
    (SuzukiSeamRoot.left, bFourSeven) ∉ suzukiAdmissibleSeamVertices bFourA := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff, coord_seven, bFourA] at h
  linarith [log_four_lt_log_seven, log_four_eq_two_log_two]

private theorem eleven_not_admissible :
    (SuzukiSeamRoot.left, bFourEleven) ∉ suzukiAdmissibleSeamVertices bFourA := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff, coord_eleven, bFourA] at h
  linarith [log_four_lt_log_eleven, log_four_eq_two_log_two]

private theorem readout_three_sub_neg_two :
    bFourReadoutThree.2 - (-bFourTwo) = bFourSeven := by
  simp only [bFourReadoutThree, bFourSourceOne]
  abel

private theorem readout_four_sub_neg_three :
    bFourReadoutFour.2 - (-bFourThree) = bFourEleven := by
  simp only [bFourReadoutFour, bFourSourceTwo]
  abel

private theorem readout_three_sub_neg_two_sub_two :
    bFourReadoutThree.2 - (-bFourTwo) - bFourTwo = bFourSourceOne.2 := by
  simp only [bFourReadoutThree, bFourSourceOne]
  abel

private theorem readout_four_sub_neg_three_sub_three :
    bFourReadoutFour.2 - (-bFourThree) - bFourThree = bFourSourceTwo.2 := by
  simp only [bFourReadoutFour, bFourSourceTwo]
  abel

private theorem off_source_three_two_ne :
    (SuzukiSeamRoot.left, bFourReadoutThree.2 - (-bFourTwo) - bFourThree) ≠ bFourSourceTwo := by
  intro h
  have hc := congrArg (fun q : SuzukiSeamVertex => primeSeamCoordinate q.2) h
  simp only [bFourReadoutThree, bFourSourceOne, bFourSourceTwo, map_sub,
    map_neg, coord_two, coord_three, coord_seven, coord_eleven] at hc
  linarith [log_seven_lt_log_eleven]

private theorem off_source_four_one_ne :
    (SuzukiSeamRoot.left, bFourReadoutFour.2 - (-bFourThree) - bFourTwo) ≠ bFourSourceOne := by
  intro h
  have hc := congrArg (fun q : SuzukiSeamVertex => primeSeamCoordinate q.2) h
  simp only [bFourReadoutFour, bFourSourceOne, bFourSourceTwo, map_sub,
    map_neg, coord_two, coord_three, coord_seven, coord_eleven] at hc
  linarith [log_seven_lt_log_eleven]

private def bFourEntry31 : ℂ :=
  suzukiPrunedBoundaryExcursion bFourA (-bFourTwo) bFourTwo
    (lp.single 2 bFourSourceOne 1) bFourReadoutThree

private def bFourEntry32 : ℂ :=
  suzukiPrunedBoundaryExcursion bFourA (-bFourTwo) bFourThree
    (lp.single 2 bFourSourceTwo 1) bFourReadoutThree

private def bFourEntry41 : ℂ :=
  suzukiPrunedBoundaryExcursion bFourA (-bFourThree) bFourTwo
    (lp.single 2 bFourSourceOne 1) bFourReadoutFour

private def bFourEntry42 : ℂ :=
  suzukiPrunedBoundaryExcursion bFourA (-bFourThree) bFourThree
    (lp.single 2 bFourSourceTwo 1) bFourReadoutFour

private theorem bFourEntry31_eq_neg_one : bFourEntry31 = -1 := by
  have hq : bFourReadoutThree ∈ suzukiAdmissibleSeamVertices bFourA := by
    simpa only [bFourReadoutThree] using source_one_admissible
  have hinter :
      (bFourReadoutThree.1, bFourReadoutThree.2 - (-bFourTwo)) =
        (SuzukiSeamRoot.left, bFourSeven) := by
    apply Prod.ext
    · rfl
    · exact readout_three_sub_neg_two
  have hsource :
      (SuzukiSeamRoot.left, bFourSeven - bFourTwo) = bFourSourceOne := by
    rfl
  unfold bFourEntry31 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem hq,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA) - 1)
        ((suzukiSeamShift bFourTwo)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceOne 1))))
        (SuzukiSeamRoot.left, bFourSeven) =
      -((suzukiSeamShift bFourTwo)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceOne 1)))
        (SuzukiSeamRoot.left, bFourSeven) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
        ((suzukiSeamShift bFourTwo)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceOne 1))))
        (SuzukiSeamRoot.left, bFourSeven) -
      ((suzukiSeamShift bFourTwo)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
          (lp.single 2 bFourSourceOne 1)))
        (SuzukiSeamRoot.left, bFourSeven) = _
    rw [lpCoordinateProjection_apply, indicator_of_notMem seven_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, hsource,
    lpCoordinateProjection_apply, indicator_of_mem source_one_admissible]
  simp [lp.single_apply]

private theorem bFourEntry42_eq_neg_one : bFourEntry42 = -1 := by
  have hq : bFourReadoutFour ∈ suzukiAdmissibleSeamVertices bFourA := by
    simpa only [bFourReadoutFour] using source_two_admissible
  have hinter :
      (bFourReadoutFour.1, bFourReadoutFour.2 - (-bFourThree)) =
        (SuzukiSeamRoot.left, bFourEleven) := by
    apply Prod.ext
    · rfl
    · exact readout_four_sub_neg_three
  have hsource :
      (SuzukiSeamRoot.left, bFourEleven - bFourThree) = bFourSourceTwo := by
    rfl
  unfold bFourEntry42 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem hq,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA) - 1)
        ((suzukiSeamShift bFourThree)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceTwo 1))))
        (SuzukiSeamRoot.left, bFourEleven) =
      -((suzukiSeamShift bFourThree)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceTwo 1)))
        (SuzukiSeamRoot.left, bFourEleven) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
        ((suzukiSeamShift bFourThree)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceTwo 1))))
        (SuzukiSeamRoot.left, bFourEleven) -
      ((suzukiSeamShift bFourThree)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
          (lp.single 2 bFourSourceTwo 1)))
        (SuzukiSeamRoot.left, bFourEleven) = _
    rw [lpCoordinateProjection_apply, indicator_of_notMem eleven_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, hsource,
    lpCoordinateProjection_apply, indicator_of_mem source_two_admissible]
  simp [lp.single_apply]

private theorem bFourEntry32_eq_zero : bFourEntry32 = 0 := by
  have hq : bFourReadoutThree ∈ suzukiAdmissibleSeamVertices bFourA := by
    simpa only [bFourReadoutThree] using source_one_admissible
  have hinter :
      (bFourReadoutThree.1, bFourReadoutThree.2 - (-bFourTwo)) =
        (SuzukiSeamRoot.left, bFourSeven) := by
    apply Prod.ext
    · rfl
    · exact readout_three_sub_neg_two
  have hzero :
      ((lp.single 2 bFourSourceTwo (1 : ℂ)) : SuzukiSeamHilbert)
        (SuzukiSeamRoot.left, bFourSeven - bFourThree) = 0 := by
    have hoff : (SuzukiSeamRoot.left, bFourSeven - bFourThree) ≠ bFourSourceTwo := by
      simpa only [readout_three_sub_neg_two] using off_source_three_two_ne
    rw [lp.single_apply, Pi.single_apply, if_neg hoff]
  have hprojected_zero :
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
        ((lp.single 2 bFourSourceTwo (1 : ℂ)) : SuzukiSeamHilbert))
        (SuzukiSeamRoot.left, bFourSeven - bFourThree) = 0 := by
    rw [lpCoordinateProjection_apply]
    by_cases hmem :
        (SuzukiSeamRoot.left, bFourSeven - bFourThree) ∈
          suzukiAdmissibleSeamVertices bFourA
    · rw [indicator_of_mem hmem, hzero]
    · rw [indicator_of_notMem hmem]
  unfold bFourEntry32 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem hq,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA) - 1)
        ((suzukiSeamShift bFourThree)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceTwo 1))))
        (SuzukiSeamRoot.left, bFourSeven) =
      -((suzukiSeamShift bFourThree)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceTwo 1)))
        (SuzukiSeamRoot.left, bFourSeven) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
        ((suzukiSeamShift bFourThree)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceTwo 1))))
        (SuzukiSeamRoot.left, bFourSeven) -
      ((suzukiSeamShift bFourThree)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
          (lp.single 2 bFourSourceTwo 1)))
        (SuzukiSeamRoot.left, bFourSeven) = _
    rw [lpCoordinateProjection_apply, indicator_of_notMem seven_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, hprojected_zero]
  norm_num

private theorem bFourEntry41_eq_zero : bFourEntry41 = 0 := by
  have hq : bFourReadoutFour ∈ suzukiAdmissibleSeamVertices bFourA := by
    simpa only [bFourReadoutFour] using source_two_admissible
  have hinter :
      (bFourReadoutFour.1, bFourReadoutFour.2 - (-bFourThree)) =
        (SuzukiSeamRoot.left, bFourEleven) := by
    apply Prod.ext
    · rfl
    · exact readout_four_sub_neg_three
  have hzero :
      ((lp.single 2 bFourSourceOne (1 : ℂ)) : SuzukiSeamHilbert)
        (SuzukiSeamRoot.left, bFourEleven - bFourTwo) = 0 := by
    have hoff : (SuzukiSeamRoot.left, bFourEleven - bFourTwo) ≠ bFourSourceOne := by
      simpa only [readout_four_sub_neg_three] using off_source_four_one_ne
    rw [lp.single_apply, Pi.single_apply, if_neg hoff]
  have hprojected_zero :
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
        ((lp.single 2 bFourSourceOne (1 : ℂ)) : SuzukiSeamHilbert))
        (SuzukiSeamRoot.left, bFourEleven - bFourTwo) = 0 := by
    rw [lpCoordinateProjection_apply]
    by_cases hmem :
        (SuzukiSeamRoot.left, bFourEleven - bFourTwo) ∈
          suzukiAdmissibleSeamVertices bFourA
    · rw [indicator_of_mem hmem, hzero]
    · rw [indicator_of_notMem hmem]
  unfold bFourEntry41 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem hq,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA) - 1)
        ((suzukiSeamShift bFourTwo)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceOne 1))))
        (SuzukiSeamRoot.left, bFourEleven) =
      -((suzukiSeamShift bFourTwo)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceOne 1)))
        (SuzukiSeamRoot.left, bFourEleven) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
        ((suzukiSeamShift bFourTwo)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
            (lp.single 2 bFourSourceOne 1))))
        (SuzukiSeamRoot.left, bFourEleven) -
      ((suzukiSeamShift bFourTwo)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices bFourA)
          (lp.single 2 bFourSourceOne 1)))
        (SuzukiSeamRoot.left, bFourEleven) = _
    rw [lpCoordinateProjection_apply, indicator_of_notMem eleven_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, hprojected_zero]
  norm_num

/-- The four literal reflected-excursion entries indexed by the two incoming and two outgoing
prime legs.  The carrier retains the excluded intermediate vertex before scalar readout. -/
def suzukiBoundaryExcursionFourLabelEntry31 : ℝ := bFourEntry31.re
def suzukiBoundaryExcursionFourLabelEntry32 : ℝ := bFourEntry32.re
def suzukiBoundaryExcursionFourLabelEntry41 : ℝ := bFourEntry41.re
def suzukiBoundaryExcursionFourLabelEntry42 : ℝ := bFourEntry42.re

/-- First four-label Pluecker minor of the literal reflected Suzuki boundary-excursion carrier. -/
def suzukiBoundaryExcursionFourLabelMinor : ℝ :=
  suzukiBoundaryExcursionFourLabelEntry31 * suzukiBoundaryExcursionFourLabelEntry42 -
    suzukiBoundaryExcursionFourLabelEntry32 * suzukiBoundaryExcursionFourLabelEntry41

theorem suzukiBoundaryExcursionFourLabelEntry31_eq_neg_one :
    suzukiBoundaryExcursionFourLabelEntry31 = -1 := by
  unfold suzukiBoundaryExcursionFourLabelEntry31
  rw [bFourEntry31_eq_neg_one]
  norm_num

theorem suzukiBoundaryExcursionFourLabelEntry32_eq_zero :
    suzukiBoundaryExcursionFourLabelEntry32 = 0 := by
  unfold suzukiBoundaryExcursionFourLabelEntry32
  rw [bFourEntry32_eq_zero]
  norm_num

theorem suzukiBoundaryExcursionFourLabelEntry41_eq_zero :
    suzukiBoundaryExcursionFourLabelEntry41 = 0 := by
  unfold suzukiBoundaryExcursionFourLabelEntry41
  rw [bFourEntry41_eq_zero]
  norm_num

theorem suzukiBoundaryExcursionFourLabelEntry42_eq_neg_one :
    suzukiBoundaryExcursionFourLabelEntry42 = -1 := by
  unfold suzukiBoundaryExcursionFourLabelEntry42
  rw [bFourEntry42_eq_neg_one]
  norm_num

/-- **Source four-label survivor.** The literal reflected Suzuki boundary-excursion carrier has
a nonzero first Pluecker minor before any scalar top-signature aggregation. -/
theorem suzukiBoundaryExcursionFourLabelMinor_eq_one :
    suzukiBoundaryExcursionFourLabelMinor = 1 := by
  unfold suzukiBoundaryExcursionFourLabelMinor
  rw [suzukiBoundaryExcursionFourLabelEntry31_eq_neg_one,
    suzukiBoundaryExcursionFourLabelEntry32_eq_zero,
    suzukiBoundaryExcursionFourLabelEntry41_eq_zero,
    suzukiBoundaryExcursionFourLabelEntry42_eq_neg_one]
  norm_num

/-- The source minor is exactly the four-label curvature invariant used by the Route-P
Pluecker carrier. -/
theorem curvatureMinor_suzukiBoundaryExcursionFourLabel_eq_one :
    GaloisForLFunctions.HTGeometry.curvatureMinor
      suzukiBoundaryExcursionFourLabelEntry31
      suzukiBoundaryExcursionFourLabelEntry32
      suzukiBoundaryExcursionFourLabelEntry41
      suzukiBoundaryExcursionFourLabelEntry42 = 1 := by
  exact suzukiBoundaryExcursionFourLabelMinor_eq_one

/-- At the fixed upper-half-plane point `(I,I)`, the literal source curvature produces a
nondegenerate rank-two Pluecker determinant. -/
theorem det_suzukiBoundaryExcursionFourLabelPlucker_at_I :
    (GaloisForLFunctions.HTGeometry.curvaturePluckerPencil
      suzukiBoundaryExcursionFourLabelEntry31
      suzukiBoundaryExcursionFourLabelEntry32
      suzukiBoundaryExcursionFourLabelEntry41
      suzukiBoundaryExcursionFourLabelEntry42 Complex.I Complex.I).det = -1 := by
  rw [GaloisForLFunctions.HTGeometry.det_curvaturePluckerPencil,
    curvatureMinor_suzukiBoundaryExcursionFourLabel_eq_one]
  norm_num [GaloisForLFunctions.HTGeometry.curvatureMinor]

end GaloisForLFunctions.RHTower
