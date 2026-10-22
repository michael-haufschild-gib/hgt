import GaloisForLFunctions.RHTower.Suzuki.SuzukiPrunedBoundaryExcursionDefect
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRootPortFirstGradeObservability

/-!
# Root-anchored weighted Suzuki boundary excursions

Strict aperture pruning annihilates a raw Suzuki endpoint trace before a boundary excursion can
see it.  This module closes that literal obstruction and its minimal repair: inject each endpoint
trace through an actual weighted prime atom first, then let two weighted reflected alphabet legs
traverse the excluded seam complement.  At aperture `log 2`, the concrete primes `2,3,5,11`
produce a nonzero two-port determinant with its exact finite Euler coefficient.

This is a finite pre-scalar source-carrier theorem.  It neither identifies the completed
prime--polar--Gamma current nor proves a cofinal signed-FU bound.
-/

open Complex Set ContinuousLinearMap

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

private def rPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
private def rPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩
private def rPrimeFive : Nat.Primes := ⟨5, Nat.prime_five⟩
private def rPrimeEleven : Nat.Primes := ⟨11, by norm_num⟩

private def rTwo : SuzukiSeamValuation := suzukiPrimePowerStep (rPrimeTwo, 1)
private def rThree : SuzukiSeamValuation := suzukiPrimePowerStep (rPrimeThree, 1)
private def rFive : SuzukiSeamValuation := suzukiPrimePowerStep (rPrimeFive, 1)
private def rEleven : SuzukiSeamValuation := suzukiPrimePowerStep (rPrimeEleven, 1)

private def rA : ℝ := Real.log 2
private def rQTwo : SuzukiSeamVertex := (SuzukiSeamRoot.left, rTwo)
private def rQThree : SuzukiSeamVertex := (SuzukiSeamRoot.left, rThree)

private def rWTwo : ℝ := suzukiPrimePowerWeight (rPrimeTwo, 1)
private def rWThree : ℝ := suzukiPrimePowerWeight (rPrimeThree, 1)
private def rWFive : ℝ := suzukiPrimePowerWeight (rPrimeFive, 1)
private def rWEleven : ℝ := suzukiPrimePowerWeight (rPrimeEleven, 1)

private theorem rcoord_two : primeSeamCoordinate rTwo = Real.log 2 := by
  simp [rTwo, rPrimeTwo, primeSeamCoordinate_primePowerStep]
private theorem rcoord_three : primeSeamCoordinate rThree = Real.log 3 := by
  simp [rThree, rPrimeThree, primeSeamCoordinate_primePowerStep]
private theorem rcoord_five : primeSeamCoordinate rFive = Real.log 5 := by
  simp [rFive, rPrimeFive, primeSeamCoordinate_primePowerStep]
private theorem rcoord_eleven : primeSeamCoordinate rEleven = Real.log 11 := by
  simp [rEleven, rPrimeEleven, primeSeamCoordinate_primePowerStep]

private theorem rlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
private theorem rlog_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
private theorem rlog_five_pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
private theorem rlog_eleven_pos : 0 < Real.log 11 := Real.log_pos (by norm_num)
private theorem rlog_two_lt_log_three : Real.log 2 < Real.log 3 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
private theorem rlog_two_lt_log_five : Real.log 2 < Real.log 5 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
private theorem rlog_four_lt_log_eleven : Real.log 4 < Real.log 11 :=
  Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
private theorem rlog_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  calc
    Real.log 4 = Real.log (2 * 2) := by norm_num
    _ = Real.log 2 + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    _ = 2 * Real.log 2 := by ring
private theorem rlog_three_lt_two_log_two : Real.log 3 < 2 * Real.log 2 := by
  have h : Real.log 3 < Real.log 4 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  linarith [rlog_four_eq_two_log_two]

private theorem rlog_two_add_log_five_lt_log_eleven :
    Real.log 2 + Real.log 5 < Real.log 11 := by
  have h : Real.log 10 < Real.log 11 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  calc
    Real.log 2 + Real.log 5 = Real.log (2 * 5) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)]; norm_num
    _ = Real.log 10 := by norm_num
    _ < Real.log 11 := h

private theorem rlog_four_add_log_five_lt_log_three_add_log_eleven :
    Real.log 4 + Real.log 5 < Real.log 3 + Real.log 11 := by
  have h : Real.log 20 < Real.log 33 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  calc
    Real.log 4 + Real.log 5 = Real.log (4 * 5) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)]; norm_num
    _ = Real.log 20 := by norm_num
    _ < Real.log 33 := h
    _ = Real.log (3 * 11) := by norm_num
    _ = Real.log 3 + Real.log 11 := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)]; norm_num

private theorem rQTwo_admissible : rQTwo ∈ suzukiAdmissibleSeamVertices rA := by
  rw [rQTwo, suzukiAdmissibleSeamVertices_iff, rcoord_two, rA]
  constructor <;> linarith [rlog_two_pos]

private theorem rQThree_admissible : rQThree ∈ suzukiAdmissibleSeamVertices rA := by
  rw [rQThree, suzukiAdmissibleSeamVertices_iff, rcoord_three, rA]
  constructor <;> linarith [rlog_three_pos, rlog_three_lt_two_log_two]

private theorem rMiddleTwoFive_not_admissible :
    (SuzukiSeamRoot.left, rTwo + rFive) ∉ suzukiAdmissibleSeamVertices rA := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff, map_add, rcoord_two, rcoord_five, rA] at h
  linarith [rlog_two_lt_log_five]

private theorem rMiddleThreeEleven_not_admissible :
    (SuzukiSeamRoot.left, rThree + rEleven) ∉ suzukiAdmissibleSeamVertices rA := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff, map_add, rcoord_three, rcoord_eleven, rA] at h
  linarith [rlog_four_lt_log_eleven, rlog_four_eq_two_log_two, rlog_three_pos]

private theorem rCrossTwoFiveEleven_not_admissible :
    (SuzukiSeamRoot.left, rTwo + rFive - rEleven) ∉ suzukiAdmissibleSeamVertices rA := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff, map_sub, map_add,
    rcoord_two, rcoord_five, rcoord_eleven] at h
  linarith [rlog_two_add_log_five_lt_log_eleven]

private theorem rCrossThreeElevenFive_not_admissible :
    (SuzukiSeamRoot.left, rThree + rEleven - rFive) ∉ suzukiAdmissibleSeamVertices rA := by
  intro h
  rw [suzukiAdmissibleSeamVertices_iff, map_sub, map_add,
    rcoord_three, rcoord_eleven, rcoord_five, rA] at h
  linarith [rlog_four_eq_two_log_two,
    rlog_four_add_log_five_lt_log_three_add_log_eleven]

private theorem rQTwo_sub_neg_five : rQTwo.2 - (-rFive) = rTwo + rFive := by
  simp only [rQTwo]
  abel

private theorem rQThree_sub_neg_eleven : rQThree.2 - (-rEleven) = rThree + rEleven := by
  simp only [rQThree]
  abel

private def rRootTwo : SuzukiSeamHilbert :=
  lpCoordinateProjection (suzukiAdmissibleSeamVertices rA)
    ((-((rWTwo : ℝ) : ℂ)) •
      suzukiSymmetricSeamStep rTwo (suzukiRootTraceVector 1 0))

private def rRootThree : SuzukiSeamHilbert :=
  lpCoordinateProjection (suzukiAdmissibleSeamVertices rA)
    ((-((rWThree : ℝ) : ℂ)) •
      suzukiSymmetricSeamStep rThree (suzukiRootTraceVector 1 0))

private theorem rRootTwo_at_qtwo : rRootTwo rQTwo = -((rWTwo : ℝ) : ℂ) := by
  unfold rRootTwo
  rw [lpCoordinateProjection_apply, indicator_of_mem rQTwo_admissible]
  change (-((rWTwo : ℝ) : ℂ)) *
      (suzukiSymmetricSeamStep rTwo (suzukiRootTraceVector 1 0)) rQTwo = _
  have hcore := suzukiFirstGrade_left_coordinate rA rTwo 1 0
      (by rw [rcoord_two]; exact rlog_two_pos)
      (by rw [rcoord_two, rA]; linarith [rlog_two_pos])
  have hmem : (SuzukiSeamRoot.left, rTwo) ∈ suzukiAdmissibleSeamVertices rA :=
    rQTwo_admissible
  rw [lpCoordinateProjection_apply] at hcore
  rw [Set.indicator_of_mem hmem] at hcore
  have hraw : (suzukiSymmetricSeamStep rTwo (suzukiRootTraceVector 1 0)) rQTwo = 1 := by
    simpa [rQTwo] using hcore
  rw [hraw]
  ring

private theorem rRootThree_at_qthree : rRootThree rQThree = -((rWThree : ℝ) : ℂ) := by
  unfold rRootThree
  rw [lpCoordinateProjection_apply, indicator_of_mem rQThree_admissible]
  change (-((rWThree : ℝ) : ℂ)) *
      (suzukiSymmetricSeamStep rThree (suzukiRootTraceVector 1 0)) rQThree = _
  have hcore := suzukiFirstGrade_left_coordinate rA rThree 1 0
      (by rw [rcoord_three]; exact rlog_three_pos)
      (by rw [rcoord_three, rA]; exact rlog_three_lt_two_log_two)
  have hmem : (SuzukiSeamRoot.left, rThree) ∈ suzukiAdmissibleSeamVertices rA :=
    rQThree_admissible
  rw [lpCoordinateProjection_apply] at hcore
  rw [Set.indicator_of_mem hmem] at hcore
  have hraw : (suzukiSymmetricSeamStep rThree (suzukiRootTraceVector 1 0)) rQThree = 1 := by
    simpa [rQThree] using hcore
  rw [hraw]
  ring

/-- A strict aperture contains neither endpoint root.  Thus direct insertion of a raw Suzuki
root trace into a pruned boundary excursion is identically annihilated. -/
theorem suzukiStrictProjection_rootTrace_eq_zero (a : ℝ) (βleft βright : ℂ) :
    lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
      (suzukiRootTraceVector βleft βright) = 0 := by
  ext q
  rw [lpCoordinateProjection_apply]
  by_cases hmem : q ∈ suzukiAdmissibleSeamVertices a
  · rw [indicator_of_mem hmem]
    have hleft : q ≠ (SuzukiSeamRoot.left, 0) := by
      intro hq
      subst q
      rw [suzukiAdmissibleSeamVertices_iff] at hmem
      simpa using hmem.1
    have hright : q ≠ (SuzukiSeamRoot.right, 0) := by
      intro hq
      subst q
      rw [suzukiAdmissibleSeamVertices_iff] at hmem
      simpa using hmem.1
    simp [suzukiRootTraceVector, lp.single_apply, hleft, hright]
  · rw [indicator_of_notMem hmem]
    simp

/-- Consequently no literal pruned boundary excursion can see a raw endpoint trace.  A physical
producer must first inject the trace by an actual prime step before the first strict projection. -/
theorem suzukiPrunedBoundaryExcursion_rootTrace_eq_zero
    (a : ℝ) (δ η : SuzukiSeamValuation) (βleft βright : ℂ) :
    suzukiPrunedBoundaryExcursion a δ η (suzukiRootTraceVector βleft βright) = 0 := by
  unfold suzukiPrunedBoundaryExcursion
  dsimp
  rw [suzukiStrictProjection_rootTrace_eq_zero]
  simp

private def rEntry31 : ℂ :=
  suzukiPrunedBoundaryExcursion rA (-rFive) rFive rRootTwo rQTwo

private def rEntry42 : ℂ :=
  suzukiPrunedBoundaryExcursion rA (-rEleven) rEleven rRootThree rQThree

private def rEntry32 : ℂ :=
  suzukiPrunedBoundaryExcursion rA (-rFive) rEleven rRootThree rQTwo

private def rEntry41 : ℂ :=
  suzukiPrunedBoundaryExcursion rA (-rEleven) rFive rRootTwo rQThree

private theorem rEntry31_eq_weight : rEntry31 = (rWTwo : ℂ) := by
  have hinter :
      (rQTwo.1, rQTwo.2 - (-rFive)) = (SuzukiSeamRoot.left, rTwo + rFive) := by
    apply Prod.ext
    · rfl
    · exact rQTwo_sub_neg_five
  have hsource :
      ((SuzukiSeamRoot.left, rTwo + rFive).1,
        (SuzukiSeamRoot.left, rTwo + rFive).2 - rFive) = rQTwo := by
    apply Prod.ext
    · rfl
    · simp only
      rw [rQTwo]
      abel
  unfold rEntry31 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem rQTwo_admissible,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) - 1)
        ((suzukiSeamShift rFive)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo)))
        (SuzukiSeamRoot.left, rTwo + rFive) =
      -((suzukiSeamShift rFive)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo))
        (SuzukiSeamRoot.left, rTwo + rFive) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA)
        ((suzukiSeamShift rFive)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo)))
        (SuzukiSeamRoot.left, rTwo + rFive) -
      ((suzukiSeamShift rFive)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo))
        (SuzukiSeamRoot.left, rTwo + rFive) = _
    rw [lpCoordinateProjection_apply,
      indicator_of_notMem rMiddleTwoFive_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, hsource,
    lpCoordinateProjection_apply, indicator_of_mem rQTwo_admissible,
    rRootTwo_at_qtwo]
  ring

private theorem rEntry42_eq_weight : rEntry42 = (rWThree : ℂ) := by
  have hinter :
      (rQThree.1, rQThree.2 - (-rEleven)) =
        (SuzukiSeamRoot.left, rThree + rEleven) := by
    apply Prod.ext
    · rfl
    · exact rQThree_sub_neg_eleven
  have hsource :
      ((SuzukiSeamRoot.left, rThree + rEleven).1,
        (SuzukiSeamRoot.left, rThree + rEleven).2 - rEleven) = rQThree := by
    apply Prod.ext
    · rfl
    · simp only
      rw [rQThree]
      abel
  unfold rEntry42 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem rQThree_admissible,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) - 1)
        ((suzukiSeamShift rEleven)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree)))
        (SuzukiSeamRoot.left, rThree + rEleven) =
      -((suzukiSeamShift rEleven)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree))
        (SuzukiSeamRoot.left, rThree + rEleven) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA)
        ((suzukiSeamShift rEleven)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree)))
        (SuzukiSeamRoot.left, rThree + rEleven) -
      ((suzukiSeamShift rEleven)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree))
        (SuzukiSeamRoot.left, rThree + rEleven) = _
    rw [lpCoordinateProjection_apply,
      indicator_of_notMem rMiddleThreeEleven_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, hsource,
    lpCoordinateProjection_apply, indicator_of_mem rQThree_admissible,
    rRootThree_at_qthree]
  ring

private theorem rEntry32_eq_zero : rEntry32 = 0 := by
  have hinter :
      (rQTwo.1, rQTwo.2 - (-rFive)) = (SuzukiSeamRoot.left, rTwo + rFive) := by
    apply Prod.ext
    · rfl
    · exact rQTwo_sub_neg_five
  unfold rEntry32 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem rQTwo_admissible,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) - 1)
        ((suzukiSeamShift rEleven)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree)))
        (SuzukiSeamRoot.left, rTwo + rFive) =
      -((suzukiSeamShift rEleven)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree))
        (SuzukiSeamRoot.left, rTwo + rFive) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA)
        ((suzukiSeamShift rEleven)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree)))
        (SuzukiSeamRoot.left, rTwo + rFive) -
      ((suzukiSeamShift rEleven)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootThree))
        (SuzukiSeamRoot.left, rTwo + rFive) = _
    rw [lpCoordinateProjection_apply,
      indicator_of_notMem rMiddleTwoFive_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, lpCoordinateProjection_apply,
    indicator_of_notMem rCrossTwoFiveEleven_not_admissible]
  norm_num

private theorem rEntry41_eq_zero : rEntry41 = 0 := by
  have hinter :
      (rQThree.1, rQThree.2 - (-rEleven)) =
        (SuzukiSeamRoot.left, rThree + rEleven) := by
    apply Prod.ext
    · rfl
    · exact rQThree_sub_neg_eleven
  unfold rEntry41 suzukiPrunedBoundaryExcursion
  dsimp
  rw [lpCoordinateProjection_apply, indicator_of_mem rQThree_admissible,
    suzukiSeamShift_apply, hinter]
  have hdefect :
      ((lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) - 1)
        ((suzukiSeamShift rFive)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo)))
        (SuzukiSeamRoot.left, rThree + rEleven) =
      -((suzukiSeamShift rFive)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo))
        (SuzukiSeamRoot.left, rThree + rEleven) := by
    rw [sub_apply]
    change
      (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA)
        ((suzukiSeamShift rFive)
          (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo)))
        (SuzukiSeamRoot.left, rThree + rEleven) -
      ((suzukiSeamShift rFive)
        (lpCoordinateProjection (suzukiAdmissibleSeamVertices rA) rRootTwo))
        (SuzukiSeamRoot.left, rThree + rEleven) = _
    rw [lpCoordinateProjection_apply,
      indicator_of_notMem rMiddleThreeEleven_not_admissible]
    ring
  rw [hdefect, suzukiSeamShift_apply, lpCoordinateProjection_apply,
    indicator_of_notMem rCrossThreeElevenFive_not_admissible]
  norm_num

/-- One literal oriented finite-prime-alphabet translation.  Its coefficient is the Wiener
atom `-(log p)/p^(j/2)`, before any scalar readout. -/
def suzukiWeightedSeamShift (w : ℝ) (δ : SuzukiSeamValuation) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  (-(w : ℂ)) • suzukiSeamShift δ

/-- The reflected excursion built from two literal weighted alphabet translations. -/
def suzukiWeightedBoundaryExcursion
    (a : ℝ) (wδ : ℝ) (δ : SuzukiSeamValuation) (wη : ℝ) (η : SuzukiSeamValuation) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  let P := lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  P ∘L suzukiWeightedSeamShift wδ δ ∘L (P - 1) ∘L suzukiWeightedSeamShift wη η ∘L P

private theorem rLp_smul_apply (c : ℂ) (g : SuzukiSeamHilbert) (q : SuzukiSeamVertex) :
    (c • g) q = c * g q := by
  rw [lp.coeFn_smul]
  simp only [Pi.smul_apply, smul_eq_mul]

theorem suzukiWeightedBoundaryExcursion_apply
    (a : ℝ) (wδ : ℝ) (δ : SuzukiSeamValuation) (wη : ℝ) (η : SuzukiSeamValuation)
    (f : SuzukiSeamHilbert) (q : SuzukiSeamVertex) :
    suzukiWeightedBoundaryExcursion a wδ δ wη η f q =
      (wδ : ℂ) * (wη : ℂ) * suzukiPrunedBoundaryExcursion a δ η f q := by
  simp only [suzukiWeightedBoundaryExcursion, suzukiWeightedSeamShift,
    ContinuousLinearMap.comp_apply, smul_apply,
    suzukiPrunedBoundaryExcursion, map_smul]
  rw [rLp_smul_apply, rLp_smul_apply]
  ring

private def rWeightedEntry31 : ℂ :=
  suzukiWeightedBoundaryExcursion rA rWFive (-rFive) rWFive rFive rRootTwo rQTwo

private theorem rWeightedEntry31_eq : rWeightedEntry31 =
    (rWFive : ℂ) * (rWFive : ℂ) * (rWTwo : ℂ) := by
  unfold rWeightedEntry31
  rw [suzukiWeightedBoundaryExcursion_apply]
  rw [show suzukiPrunedBoundaryExcursion rA (-rFive) rFive rRootTwo rQTwo = rEntry31 by rfl]
  rw [rEntry31_eq_weight]

private def rWeightedEntry32 : ℂ :=
  suzukiWeightedBoundaryExcursion rA rWFive (-rFive) rWEleven rEleven rRootThree rQTwo

private def rWeightedEntry41 : ℂ :=
  suzukiWeightedBoundaryExcursion rA rWEleven (-rEleven) rWFive rFive rRootTwo rQThree

private def rWeightedEntry42 : ℂ :=
  suzukiWeightedBoundaryExcursion rA rWEleven (-rEleven) rWEleven rEleven rRootThree rQThree

private theorem rWeightedEntry32_eq_zero : rWeightedEntry32 = 0 := by
  unfold rWeightedEntry32
  rw [suzukiWeightedBoundaryExcursion_apply]
  rw [show suzukiPrunedBoundaryExcursion rA (-rFive) rEleven rRootThree rQTwo = rEntry32 by rfl]
  rw [rEntry32_eq_zero, mul_zero]

private theorem rWeightedEntry41_eq_zero : rWeightedEntry41 = 0 := by
  unfold rWeightedEntry41
  rw [suzukiWeightedBoundaryExcursion_apply]
  rw [show suzukiPrunedBoundaryExcursion rA (-rEleven) rFive rRootTwo rQThree = rEntry41 by rfl]
  rw [rEntry41_eq_zero, mul_zero]

private theorem rWeightedEntry42_eq : rWeightedEntry42 =
    (rWEleven : ℂ) * (rWEleven : ℂ) * (rWThree : ℂ) := by
  unfold rWeightedEntry42
  rw [suzukiWeightedBoundaryExcursion_apply]
  rw [show suzukiPrunedBoundaryExcursion rA (-rEleven) rEleven rRootThree rQThree = rEntry42 by rfl]
  rw [rEntry42_eq_weight]

private theorem rWeightTwo_pos : 0 < rWTwo := by
  unfold rWTwo suzukiPrimePowerWeight rPrimeTwo
  have hlog : 0 < Real.log 2 := rlog_two_pos
  have hpow : 0 < (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

private theorem rWeightThree_pos : 0 < rWThree := by
  unfold rWThree suzukiPrimePowerWeight rPrimeThree
  have hlog : 0 < Real.log 3 := rlog_three_pos
  have hpow : 0 < (3 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

private theorem rWeightFive_pos : 0 < rWFive := by
  unfold rWFive suzukiPrimePowerWeight rPrimeFive
  have hlog : 0 < Real.log 5 := rlog_five_pos
  have hpow : 0 < (5 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

private theorem rWeightEleven_pos : 0 < rWEleven := by
  unfold rWEleven suzukiPrimePowerWeight rPrimeEleven
  have hlog : 0 < Real.log 11 := rlog_eleven_pos
  have hpow : 0 < (11 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  positivity

private def rWeightedMinor : ℂ :=
  rWeightedEntry31 * rWeightedEntry42 - rWeightedEntry32 * rWeightedEntry41

private theorem rWeightedMinor_eq : rWeightedMinor =
    (rWTwo : ℂ) * (rWThree : ℂ) * (rWFive : ℂ) ^ 2 * (rWEleven : ℂ) ^ 2 := by
  unfold rWeightedMinor
  rw [rWeightedEntry31_eq, rWeightedEntry32_eq_zero,
    rWeightedEntry41_eq_zero, rWeightedEntry42_eq]
  ring

private theorem rWeightedMinor_ne_zero : rWeightedMinor ≠ 0 := by
  rw [rWeightedMinor_eq]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast ne_of_gt rWeightTwo_pos
      · exact_mod_cast ne_of_gt rWeightThree_pos
    · exact pow_ne_zero _ (by exact_mod_cast ne_of_gt rWeightFive_pos)
  · exact pow_ne_zero _ (by exact_mod_cast ne_of_gt rWeightEleven_pos)

/-- The four literal source-rooted weighted boundary entries.  Every entry starts from Suzuki's
endpoint trace, is injected by its own visible prime atom before strict pruning, and keeps both
outer reflected legs in the finite prime alphabet. -/
def suzukiRootAnchoredWeightedBoundaryEntry31 : ℂ := rWeightedEntry31
def suzukiRootAnchoredWeightedBoundaryEntry32 : ℂ := rWeightedEntry32
def suzukiRootAnchoredWeightedBoundaryEntry41 : ℂ := rWeightedEntry41
def suzukiRootAnchoredWeightedBoundaryEntry42 : ℂ := rWeightedEntry42

/-- Determinant of the rooted, coefficient-faithful two-port boundary source matrix. -/
def suzukiRootAnchoredWeightedBoundaryMinor : ℂ :=
  suzukiRootAnchoredWeightedBoundaryEntry31 * suzukiRootAnchoredWeightedBoundaryEntry42 -
    suzukiRootAnchoredWeightedBoundaryEntry32 * suzukiRootAnchoredWeightedBoundaryEntry41

theorem suzukiRootAnchoredWeightedBoundaryEntry31_eq :
    suzukiRootAnchoredWeightedBoundaryEntry31 =
      (rWFive : ℂ) * (rWFive : ℂ) * (rWTwo : ℂ) :=
  rWeightedEntry31_eq

theorem suzukiRootAnchoredWeightedBoundaryEntry32_eq_zero :
    suzukiRootAnchoredWeightedBoundaryEntry32 = 0 :=
  rWeightedEntry32_eq_zero

theorem suzukiRootAnchoredWeightedBoundaryEntry41_eq_zero :
    suzukiRootAnchoredWeightedBoundaryEntry41 = 0 :=
  rWeightedEntry41_eq_zero

theorem suzukiRootAnchoredWeightedBoundaryEntry42_eq :
    suzukiRootAnchoredWeightedBoundaryEntry42 =
      (rWEleven : ℂ) * (rWEleven : ℂ) * (rWThree : ℂ) :=
  rWeightedEntry42_eq

/-- Exact coefficient retained by the rooted four-label source minor. -/
theorem suzukiRootAnchoredWeightedBoundaryMinor_eq :
    suzukiRootAnchoredWeightedBoundaryMinor =
      (rWTwo : ℂ) * (rWThree : ℂ) * (rWFive : ℂ) ^ 2 * (rWEleven : ℂ) ^ 2 :=
  rWeightedMinor_eq

/-- **Root-anchored source survivor.** The literal finite-prime two-port source matrix is
nondegenerate before any scalar completed-current readout. -/
theorem suzukiRootAnchoredWeightedBoundaryMinor_ne_zero :
    suzukiRootAnchoredWeightedBoundaryMinor ≠ 0 :=
  rWeightedMinor_ne_zero

end GaloisForLFunctions.RHTower
