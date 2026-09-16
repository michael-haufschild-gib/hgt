import GaloisForLFunctions.RHTower.CCMGuinandWeilThirdGradeCompletedQuantileTransport
import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentOutgoingChargeHankel
import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.CCMUnitRieszSuzukiGreenProducerClassification

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

end RHTower
