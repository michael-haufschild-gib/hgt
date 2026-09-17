import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCompletedQuantileTransport
import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentOutgoingChargeHankel
import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.CCMUnitRieszSuzukiGreenProducerClassification
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCoordinateTransport

/-!
# SP-E: source-faithful quantile Riesz transport

The actual outgoing prime mass defines consecutive quantile cells.  This module identifies the
unique order-one Riesz profile on those cells whose completed signed transport is the literal
critical-Mellin resolvent source at an integer aperture.  The terminal seam vanishes at the
physical wall, but the lower interval `[0, 1]` contributes the explicit correction
`2 * (sqrt M - 2 / 3)`; retaining that term is necessary for exact equality.

Thus the remaining SP-E estimate is a bound on one labelled, oriented prime--polar transport
current.  No absolute value is taken before the cells and their seam are assembled.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- Riesz profile whose prime-atom pairing is the order-one square-root window at aperture `M`. -/
def speQuantileRieszProfile (M : ℕ) (h : ℝ) : ℝ :=
  2 * (Real.sqrt (M : ℝ) * Real.exp (h / 2) - Real.exp h)

/-- The source-forced Riesz profile in canonical polar mass coordinate `Y = 2 exp(h / 2)`. -/
def speQuantileRieszMassProfile (M : ℕ) (y : ℝ) : ℝ :=
  y * Real.sqrt (M : ℝ) - y ^ 2 / 2

/-- A primitive of the mass-coordinate Riesz profile. -/
def speQuantileRieszMassAntiderivative (M : ℕ) (y : ℝ) : ℝ :=
  Real.sqrt (M : ℝ) * y ^ 2 / 2 - y ^ 3 / 6

/-- The arithmetic node `log n` in canonical polar mass coordinate. -/
def speQuantileRieszMassNode (n : ℕ) : ℝ :=
  2 * Real.sqrt (n : ℝ)

/-- Center of the literal outgoing quantile cell in canonical polar mass coordinate. -/
def speQuantileRieszMassCellCenter (n : ℕ) : ℝ :=
  ccmActualHeadQuantilePolarCoordinate n + criticalMellinAtomWeight n / 2

/-- Signed displacement from a literal quantile-cell center to its arithmetic mass node. -/
def speQuantileRieszMassCellDisplacement (n : ℕ) : ℝ :=
  speQuantileRieszMassNode n - speQuantileRieszMassCellCenter n

/-- Completed actual-quantile transport for the SP-E Riesz profile, with the forced lower-edge
correction restoring the physical source interval below logarithmic height zero. -/
def speCompletedQuantileRieszTransport (M : ℕ) : ℝ :=
  ccmPrimePolarReporterCompletedQuantileTransport
    (speQuantileRieszProfile M) M (Real.log M) -
    2 * (Real.sqrt (M : ℝ) - 2 / 3)

theorem continuous_speQuantileRieszProfile (M : ℕ) :
    Continuous (speQuantileRieszProfile M) := by
  unfold speQuantileRieszProfile
  fun_prop

theorem speQuantileRieszProfile_log_eq_zero
    {M : ℕ} (hM : 0 < M) :
    speQuantileRieszProfile M (Real.log M) = 0 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  unfold speQuantileRieszProfile
  rw [hhalf, Real.exp_log hMR]
  nlinarith [Real.sq_sqrt hMR.le]

theorem criticalMellinAtomWeight_mul_speQuantileRieszProfile_log
    (M : ℕ) {n : ℕ} (hn : 0 < n) :
    criticalMellinAtomWeight n * speQuantileRieszProfile M (Real.log n) =
      2 * ArithmeticFunction.vonMangoldt n *
        (Real.sqrt (M : ℝ) - Real.sqrt n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hhalf : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt (n : ℝ) := by
    rw [← Real.log_sqrt hnR.le, Real.exp_log hsqrt]
  have hweight : ((n : ℝ) ^ (-1 / 2 : ℝ)) = (Real.sqrt n)⁻¹ := by
    calc
      ((n : ℝ) ^ (-1 / 2 : ℝ)) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        congr 1
        ring
      _ = ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hnR.le _
      _ = (Real.sqrt n)⁻¹ := by rw [Real.sqrt_eq_rpow]
  rw [criticalMellinAtomWeight, hweight,
    speQuantileRieszProfile, hhalf, Real.exp_log hnR]
  field_simp [hsqrt.ne']
  have hsquare : Real.sqrt (n : ℝ) * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt hnR.le
  calc
    ArithmeticFunction.vonMangoldt n * (Real.sqrt n * Real.sqrt M - (n : ℝ)) =
        ArithmeticFunction.vonMangoldt n *
          (Real.sqrt n * Real.sqrt M - Real.sqrt n * Real.sqrt n) := by rw [hsquare]
    _ = Real.sqrt n * ArithmeticFunction.vonMangoldt n *
          (Real.sqrt M - Real.sqrt n) := by ring

/-- The source atom is the mass-coordinate Riesz profile evaluated at its arithmetic node. -/
theorem criticalMellinAtomWeight_mul_speQuantileRieszProfile_eq_massNode
    (M n : ℕ) :
    criticalMellinAtomWeight n * speQuantileRieszProfile M (Real.log n) =
      criticalMellinAtomWeight n *
        speQuantileRieszMassProfile M (speQuantileRieszMassNode n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : criticalMellinAtomWeight (0 : ℕ) = 0 := by
      simp [criticalMellinAtomWeight]
    rw [hzero]
    ring
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
    have hhalf : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt (n : ℝ) := by
      rw [← Real.log_sqrt hnR.le, Real.exp_log hsqrt]
    have hsquare : Real.sqrt (n : ℝ) * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt hnR.le
    have hmass : speQuantileRieszMassProfile M (speQuantileRieszMassNode n) =
        2 * (Real.sqrt (M : ℝ) * Real.sqrt n - (n : ℝ)) := by
      unfold speQuantileRieszMassProfile speQuantileRieszMassNode
      rw [show (2 * Real.sqrt (n : ℝ)) ^ 2 =
          4 * (Real.sqrt (n : ℝ) * Real.sqrt n) by ring, hsquare]
      ring
    rw [speQuantileRieszProfile, hhalf, Real.exp_log hnR, hmass]

/-- Exact mass-coordinate primitive for one literal outgoing Riesz quantile cell. -/
theorem speQuantileRieszCellIntegral_eq_massAntiderivative
    (M n : ℕ) :
    (∫ h in ccmOutgoingPrimeQuantileBoundary n..
        ccmOutgoingPrimeQuantileBoundary (n + 1),
      Real.exp (h / 2) * speQuantileRieszProfile M h) =
      speQuantileRieszMassAntiderivative M
          (ccmActualHeadQuantilePolarCoordinate (n + 1)) -
        speQuantileRieszMassAntiderivative M
          (ccmActualHeadQuantilePolarCoordinate n) := by
  let b0 := ccmOutgoingPrimeQuantileBoundary n
  let b1 := ccmOutgoingPrimeQuantileBoundary (n + 1)
  let P : ℝ → ℝ := fun h =>
    2 * Real.sqrt (M : ℝ) * Real.exp h -
      (4 / 3 : ℝ) * Real.exp (h * 3 / 2)
  let G : ℝ → ℝ := fun h => Real.exp (h / 2) * speQuantileRieszProfile M h
  have hderiv : ∀ h ∈ uIcc b0 b1, HasDerivAt P (G h) h := by
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
    have hsquareexp : Real.exp (h / 2) ^ 2 = Real.exp h := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      2 * Real.sqrt (M : ℝ) * Real.exp h -
          (4 / 3 : ℝ) * ((3 / 2 : ℝ) *
            (Real.exp h * Real.exp (h / 2))) =
          2 * Real.sqrt (M : ℝ) * Real.exp h -
            2 * Real.exp h * Real.exp (h / 2) := by ring
      _ = 2 * Real.sqrt (M : ℝ) * Real.exp (h / 2) ^ 2 -
            2 * Real.exp h * Real.exp (h / 2) := by rw [hsquareexp]
      _ = Real.exp (h / 2) *
            (2 * (Real.sqrt (M : ℝ) * Real.exp (h / 2) - Real.exp h)) := by ring
  have hint : IntervalIntegrable G volume b0 b1 := by
    dsimp only [G]
    exact ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (continuous_speQuantileRieszProfile M)).intervalIntegrable _ _
  have hprimitive :
      (∫ h in b0..b1, Real.exp (h / 2) * speQuantileRieszProfile M h) = P b1 - P b0 := by
    rw [show (fun h : ℝ => Real.exp (h / 2) * speQuantileRieszProfile M h) = G by rfl]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hP (h : ℝ) :
      P h = speQuantileRieszMassAntiderivative M (ccmActualHeadPolarMassCoordinate h) := by
    dsimp only [P, speQuantileRieszMassAntiderivative, ccmActualHeadPolarMassCoordinate]
    have hsq : Real.exp (h / 2) ^ 2 = Real.exp h := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hcub : Real.exp (h / 2) ^ 3 = Real.exp (h * 3 / 2) := by
      rw [pow_three, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [← hsq, ← hcub]
    ring
  change (∫ h in b0..b1, Real.exp (h / 2) * speQuantileRieszProfile M h) = _
  rw [hprimitive, hP, hP]
  rfl

/-- The signed atom-minus-continuum form is exactly the literal reporter cell. -/
theorem speQuantileRieszAtom_sub_cellIntegral_eq_reporterTransport
    (M n : ℕ) :
    criticalMellinAtomWeight n * speQuantileRieszProfile M (Real.log n) -
        (∫ h in ccmOutgoingPrimeQuantileBoundary n..
          ccmOutgoingPrimeQuantileBoundary (n + 1),
          Real.exp (h / 2) * speQuantileRieszProfile M h) =
      ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n := by
  let lo := ccmOutgoingPrimeQuantileBoundary n
  let hi := ccmOutgoingPrimeQuantileBoundary (n + 1)
  have hweight : Continuous (fun h : ℝ => Real.exp (h / 2)) := by fun_prop
  have hconst : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * speQuantileRieszProfile M (Real.log n)) volume lo hi :=
    (hweight.mul continuous_const).intervalIntegrable _ _
  have hvar : IntervalIntegrable
      (fun h : ℝ => Real.exp (h / 2) * speQuantileRieszProfile M h) volume lo hi :=
    (hweight.mul (continuous_speQuantileRieszProfile M)).intervalIntegrable _ _
  have hmass := integral_exp_half_quantileCell_eq_atomWeight n
  have hfirst :
      (∫ h in lo..hi, Real.exp (h / 2) * speQuantileRieszProfile M (Real.log n)) =
        criticalMellinAtomWeight n * speQuantileRieszProfile M (Real.log n) := by
    calc
      _ = speQuantileRieszProfile M (Real.log n) * ∫ h in lo..hi, Real.exp (h / 2) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro h hh
        ring
      _ = _ := by rw [hmass]; ring
  rw [ccmPrimePolarReporterQuantileCellTransport]
  calc
    criticalMellinAtomWeight n * speQuantileRieszProfile M (Real.log n) -
        (∫ h in lo..hi, Real.exp (h / 2) * speQuantileRieszProfile M h) =
      (∫ h in lo..hi, Real.exp (h / 2) * speQuantileRieszProfile M (Real.log n)) -
        ∫ h in lo..hi, Real.exp (h / 2) * speQuantileRieszProfile M h := by rw [hfirst]
    _ = ∫ h in lo..hi,
        (Real.exp (h / 2) * speQuantileRieszProfile M (Real.log n) -
          Real.exp (h / 2) * speQuantileRieszProfile M h) :=
      (intervalIntegral.integral_sub hconst hvar).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro h hh
      ring

/-- Exact source normal form of one literal SP-E reporter cell: signed node-to-center
orientation plus its forced cubic concavity reserve. -/
theorem speQuantileRieszReporterCell_eq_signedDisplacement
    (M n : ℕ) :
    ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n =
      criticalMellinAtomWeight n * speQuantileRieszMassCellDisplacement n *
          (Real.sqrt (M : ℝ) -
            (speQuantileRieszMassNode n + speQuantileRieszMassCellCenter n) / 2) +
        criticalMellinAtomWeight n ^ 3 / 24 := by
  rw [← speQuantileRieszAtom_sub_cellIntegral_eq_reporterTransport]
  rw [criticalMellinAtomWeight_mul_speQuantileRieszProfile_eq_massNode,
    speQuantileRieszCellIntegral_eq_massAntiderivative]
  have hstep := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  have hcoord : ccmActualHeadQuantilePolarCoordinate (n + 1) =
      ccmActualHeadQuantilePolarCoordinate n + criticalMellinAtomWeight n := by
    linarith
  simp only [speQuantileRieszMassProfile, speQuantileRieszMassAntiderivative,
    speQuantileRieszMassNode, speQuantileRieszMassCellCenter,
    speQuantileRieszMassCellDisplacement]
  rw [hcoord]
  ring

/-- The source displacement is the completed outgoing node error plus the forced half-atom
centering shift. -/
theorem speQuantileRieszMassCellDisplacement_eq_outgoingNodeError_add_half
    {n : ℕ} (hn : 0 < n) :
    speQuantileRieszMassCellDisplacement n =
      ccmActualHeadOutgoingNodeError n + criticalMellinAtomWeight n / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hhalf : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt (n : ℝ) := by
    rw [← Real.log_sqrt hnR.le, Real.exp_log hsqrt]
  have herror := two_exp_log_half_sub_quantile_succ_eq_outgoingNodeError n hn
  have hstep := ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight n
  unfold speQuantileRieszMassCellDisplacement speQuantileRieszMassNode
    speQuantileRieszMassCellCenter
  rw [← hhalf]
  linarith

theorem sum_range_criticalMellinAtomWeight_mul_speQuantileRieszProfile_log
    {M : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range M,
      criticalMellinAtomWeight n * speQuantileRieszProfile M (Real.log n)) =
      2 * ∑ n ∈ Finset.Icc 1 (M - 1),
        ArithmeticFunction.vonMangoldt n *
          (Real.sqrt (M : ℝ) - Real.sqrt n) := by
  have hrange : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert]
  · have hzero : criticalMellinAtomWeight (0 : ℕ) = 0 := by
      simp [criticalMellinAtomWeight]
    rw [hzero, zero_mul, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [criticalMellinAtomWeight_mul_speQuantileRieszProfile_log M hnpos]
    ring
  · simp

theorem intervalIntegral_exp_half_mul_speQuantileRieszProfile
    {M : ℕ} (hM : 0 < M) :
    (∫ h in (0 : ℝ)..Real.log M,
      Real.exp (h / 2) * speQuantileRieszProfile M h) =
      2 * ((M : ℝ) * Real.sqrt M / 3 - Real.sqrt M + 2 / 3) := by
  let P : ℝ → ℝ := fun h =>
    2 * Real.sqrt (M : ℝ) * Real.exp h -
      (4 / 3 : ℝ) * Real.exp (h * 3 / 2)
  let G : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * speQuantileRieszProfile M h
  have hderiv : ∀ h ∈ uIcc (0 : ℝ) (Real.log M), HasDerivAt P (G h) h := by
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
    have hsquareexp : Real.exp (h / 2) ^ 2 = Real.exp h := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      2 * Real.sqrt (M : ℝ) * Real.exp h -
          (4 / 3 : ℝ) * ((3 / 2 : ℝ) *
            (Real.exp h * Real.exp (h / 2))) =
          2 * Real.sqrt (M : ℝ) * Real.exp h -
            2 * Real.exp h * Real.exp (h / 2) := by ring
      _ = 2 * Real.sqrt (M : ℝ) * Real.exp (h / 2) ^ 2 -
            2 * Real.exp h * Real.exp (h / 2) := by rw [hsquareexp]
      _ = Real.exp (h / 2) *
            (2 * (Real.sqrt (M : ℝ) * Real.exp (h / 2) - Real.exp h)) := by ring
  have hint : IntervalIntegrable G volume 0 (Real.log M) := by
    dsimp only [G]
    exact ((by fun_prop : Continuous fun h : ℝ => Real.exp (h / 2)).mul
      (continuous_speQuantileRieszProfile M)).intervalIntegrable _ _
  rw [show (fun h : ℝ => Real.exp (h / 2) * speQuantileRieszProfile M h) = G by rfl]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  have hthree : Real.exp (Real.log (M : ℝ) * 3 / 2) =
      (M : ℝ) * Real.sqrt M := by
    rw [show Real.log (M : ℝ) * 3 / 2 = Real.log M + Real.log M / 2 by ring,
      Real.exp_add, Real.exp_log hMR, hhalf]
  dsimp only [P]
  rw [Real.exp_log hMR, hthree]
  norm_num
  ring

/-- The completed quantile Riesz current is exactly the integer-aperture critical-Mellin source.
Every prime label remains in a quantile cell; the terminal seam is present before its profile-zero
cancellation, and the lower-edge correction is retained explicitly. -/
theorem speCompletedQuantileRieszTransport_eq_resolvent_source
    {M : ℕ} (hM : 2 ≤ M) :
    speCompletedQuantileRieszTransport M =
      (M : ℝ) * criticalMellinChebyshevResolventSource (Real.log M) := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : 0 < M := by omega
  unfold speCompletedQuantileRieszTransport
  rw [ccmPrimePolarReporterCompletedQuantileTransport_eq
    (speQuantileRieszProfile M) (continuous_speQuantileRieszProfile M) M (Real.log M)]
  rw [speQuantileRieszProfile_log_eq_zero hM0, mul_zero, add_zero,
    sum_range_criticalMellinAtomWeight_mul_speQuantileRieszProfile_log hM1,
    intervalIntegral_exp_half_mul_speQuantileRieszProfile hM0]
  have hsum :
      (∑ n ∈ Finset.Icc 1 (M - 1),
        ArithmeticFunction.vonMangoldt n *
          (Real.sqrt (M : ℝ) - Real.sqrt n)) =
        coherentSelbergSquareRootAbelMoment M +
          ∑ n ∈ Finset.Icc 1 (M - 1),
            (Real.sqrt (M : ℝ) - Real.sqrt n) := by
    rw [← sum_vonMangoldt_sub_one_mul_sqrtGap_eq_coherentAbel M,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hcurrent :
      2 * ∑ n ∈ Finset.Icc 1 (M - 1),
        ArithmeticFunction.vonMangoldt n *
          (Real.sqrt (M : ℝ) - Real.sqrt n) -
          2 * ((M : ℝ) * Real.sqrt M / 3 - Real.sqrt M + 2 / 3) -
          2 * (Real.sqrt M - 2 / 3) =
        2 * (coherentSelbergSquareRootAbelMoment M +
          coherentSquareRootPolarLatticeDefect M) := by
    rw [hsum, coherentSquareRootPolarLatticeDefect]
    ring
  rw [hcurrent]
  have hcharge := coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect hM
  have hres := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM
  calc
    2 * (coherentSelbergSquareRootAbelMoment M +
        coherentSquareRootPolarLatticeDefect M) =
        2 * ((M : ℝ) * unitRieszCoherentCompletedOutgoingCharge M) := by rw [hcharge]
    _ = (M : ℝ) * criticalMellinChebyshevResolventSource (Real.log M) := by
      rw [hres]
      ring

/-- The full labelled quantile--Riesz transport is exactly twice the completed signed Abel
action, including the polar-lattice correction.  Thus no terminal seam or quantile-cell term is
discarded before comparison with the literal SP-E source. -/
theorem speCompletedQuantileRieszTransport_eq_two_mul_coherentSelbergAbel_add_polar
    {M : ℕ} (hM : 2 ≤ M) :
    speCompletedQuantileRieszTransport M =
      2 * (coherentSelbergSquareRootAbelMoment M +
        coherentSquareRootPolarLatticeDefect M) := by
  calc
    speCompletedQuantileRieszTransport M =
        (M : ℝ) * criticalMellinChebyshevResolventSource (Real.log M) :=
      speCompletedQuantileRieszTransport_eq_resolvent_source hM
    _ = 2 * ((M : ℝ) * unitRieszCoherentCompletedOutgoingCharge M) := by
      rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hM]
      ring
    _ = 2 * (coherentSelbergSquareRootAbelMoment M +
        coherentSquareRootPolarLatticeDefect M) := by
      rw [coherentCompletedOutgoing_mul_eq_abel_add_latticeDefect hM]

theorem speCompletedQuantileRieszTransport_div_eq_resolvent_source
    {M : ℕ} (hM : 2 ≤ M) :
    speCompletedQuantileRieszTransport M / (M : ℝ) =
      criticalMellinChebyshevResolventSource (Real.log M) := by
  rw [speCompletedQuantileRieszTransport_eq_resolvent_source hM]
  field_simp

/-- Uniform boundedness of the completed, labelled SP-E quantile Riesz transport. -/
def SPECompletedQuantileRieszTransportBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 2 ≤ M →
    |speCompletedQuantileRieszTransport M / (M : ℝ)| ≤ B

theorem riemannHypothesis_iff_SPECompletedQuantileRieszTransportBounded :
    RiemannHypothesis ↔ SPECompletedQuantileRieszTransportBounded := by
  constructor
  · intro hRH
    obtain ⟨B, hB, hsource⟩ :=
      riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mp hRH
    exact ⟨B, hB, fun M hM => by
      rw [speCompletedQuantileRieszTransport_div_eq_resolvent_source hM]
      exact hsource M hM⟩
  · rintro ⟨B, hB, htransport⟩
    apply riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mpr
    exact ⟨B, hB, fun M hM => by
      rw [← speCompletedQuantileRieszTransport_div_eq_resolvent_source hM]
      exact htransport M hM⟩

/-- The Riesz profile is nonnegative up to its physical aperture wall. -/
theorem speQuantileRieszProfile_nonneg_of_le_log
    {M : ℕ} (hM : 0 < M) {h : ℝ} (hh : h ≤ Real.log M) :
    0 ≤ speQuantileRieszProfile M h := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  have hle : Real.exp (h / 2) ≤ Real.sqrt (M : ℝ) := by
    rw [← hhalf]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp h = Real.exp (h / 2) * Real.exp (h / 2) := by
    calc
      Real.exp h = Real.exp (h / 2 + h / 2) := by
        congr 1
        ring
      _ = Real.exp (h / 2) * Real.exp (h / 2) := Real.exp_add _ _
  unfold speQuantileRieszProfile
  rw [hsq]
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_nonneg (h / 2))
  nlinarith

/-- The Riesz profile is nonpositive beyond its physical aperture wall. -/
theorem speQuantileRieszProfile_nonpos_of_log_le
    {M : ℕ} (hM : 0 < M) {h : ℝ} (hh : Real.log M ≤ h) :
    speQuantileRieszProfile M h ≤ 0 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsqrt : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr hMR
  have hhalf : Real.exp (Real.log (M : ℝ) / 2) = Real.sqrt (M : ℝ) := by
    rw [← Real.log_sqrt hMR.le, Real.exp_log hsqrt]
  have hle : Real.sqrt (M : ℝ) ≤ Real.exp (h / 2) := by
    rw [← hhalf]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsq : Real.exp h = Real.exp (h / 2) * Real.exp (h / 2) := by
    calc
      Real.exp h = Real.exp (h / 2 + h / 2) := by
        congr 1
        ring
      _ = Real.exp (h / 2) * Real.exp (h / 2) := Real.exp_add _ _
  unfold speQuantileRieszProfile
  rw [hsq]
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_nonneg (h / 2))
  nlinarith

/-- The completed quantile seam is never positive for the source-forced Riesz profile.
The remaining SP-E cancellation problem therefore lies in the labelled interior cells. -/
theorem speQuantileRieszTerminalTransport_nonpos
    {M : ℕ} (hM : 0 < M) :
    ccmPrimePolarReporterQuantileTerminalTransport
      (speQuantileRieszProfile M) M (Real.log M) ≤ 0 := by
  unfold ccmPrimePolarReporterQuantileTerminalTransport
  rw [speQuantileRieszProfile_log_eq_zero hM]
  by_cases hle : ccmOutgoingPrimeQuantileBoundary M ≤ Real.log M
  · apply neg_nonneg.mp
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_nonneg hle
    intro h hh
    calc
      0 ≤ Real.exp (h / 2) * speQuantileRieszProfile M h :=
        mul_nonneg (Real.exp_nonneg _) (speQuantileRieszProfile_nonneg_of_le_log hM hh.2)
      _ = -(Real.exp (h / 2) * (0 - speQuantileRieszProfile M h)) := by ring
  · have hle' : Real.log M ≤ ccmOutgoingPrimeQuantileBoundary M := le_of_not_ge hle
    rw [intervalIntegral.integral_symm]
    apply neg_nonpos.mpr
    apply intervalIntegral.integral_nonneg hle'
    intro h hh
    exact mul_nonneg (Real.exp_nonneg _) (by
      linarith [speQuantileRieszProfile_nonpos_of_log_le hM hh.1])

/-- The signed interior cells, before the terminal seam, of the source-forced Riesz transport. -/
def speQuantileRieszInteriorTransport (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M,
    ccmPrimePolarReporterQuantileCellTransport (speQuantileRieszProfile M) n

/-- Exact finite source normal form of the labelled SP-E interior: each cell retains its signed
node-to-center orientation and its cubic concavity reserve. -/
def speQuantileRieszInteriorSignedDisplacementNormalForm (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M,
    (criticalMellinAtomWeight n * speQuantileRieszMassCellDisplacement n *
        (Real.sqrt (M : ℝ) -
          (speQuantileRieszMassNode n + speQuantileRieszMassCellCenter n) / 2) +
      criticalMellinAtomWeight n ^ 3 / 24)

theorem speQuantileRieszInteriorTransport_eq_signedDisplacementNormalForm
    (M : ℕ) :
    speQuantileRieszInteriorTransport M =
      speQuantileRieszInteriorSignedDisplacementNormalForm M := by
  unfold speQuantileRieszInteriorTransport speQuantileRieszInteriorSignedDisplacementNormalForm
  apply Finset.sum_congr rfl
  intro n hn
  exact speQuantileRieszReporterCell_eq_signedDisplacement M n

/-- Finite completed-error form of the SP-E interior current. The orientation field is exactly
the outgoing node error; the only local correction is the forced half-atom centering shift. -/
def speQuantileRieszInteriorOutgoingNodeErrorNormalForm (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (M - 1),
    (criticalMellinAtomWeight n *
        (ccmActualHeadOutgoingNodeError n + criticalMellinAtomWeight n / 2) *
        (Real.sqrt (M : ℝ) -
          (speQuantileRieszMassNode n + speQuantileRieszMassCellCenter n) / 2) +
      criticalMellinAtomWeight n ^ 3 / 24)

theorem speQuantileRieszInteriorTransport_eq_outgoingNodeErrorNormalForm
    {M : ℕ} (hM : 1 ≤ M) :
    speQuantileRieszInteriorTransport M =
      speQuantileRieszInteriorOutgoingNodeErrorNormalForm M := by
  rw [speQuantileRieszInteriorTransport_eq_signedDisplacementNormalForm]
  unfold speQuantileRieszInteriorSignedDisplacementNormalForm
    speQuantileRieszInteriorOutgoingNodeErrorNormalForm
  have hrange : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert]
  · have hzero : criticalMellinAtomWeight (0 : ℕ) = 0 := by
      simp [criticalMellinAtomWeight]
    rw [hzero]
    norm_num
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    rw [speQuantileRieszMassCellDisplacement_eq_outgoingNodeError_add_half hnpos]
  · simp

/-- The terminal seam has no positive contribution.  Thus the completed source is bounded above
by its labelled interior cells and the explicit lower-edge correction. -/
theorem speCompletedQuantileRieszTransport_le_interior
    {M : ℕ} (hM : 2 ≤ M) :
    speCompletedQuantileRieszTransport M ≤
      speQuantileRieszInteriorTransport M - 2 * (Real.sqrt M - 2 / 3) := by
  have hterm := speQuantileRieszTerminalTransport_nonpos (M := M) (by omega : 0 < M)
  unfold speCompletedQuantileRieszTransport speQuantileRieszInteriorTransport
    ccmPrimePolarReporterCompletedQuantileTransport
  linarith

/-- Direct one-sided source reduction to the labelled SP-E interior Riesz cells. -/
theorem criticalMellinChebyshevResolventSource_mul_nat_le_speQuantileRieszInterior
    {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) * criticalMellinChebyshevResolventSource (Real.log M) ≤
      speQuantileRieszInteriorTransport M - 2 * (Real.sqrt M - 2 / 3) := by
  rw [← speCompletedQuantileRieszTransport_eq_resolvent_source hM]
  exact speCompletedQuantileRieszTransport_le_interior hM

end RHTower
