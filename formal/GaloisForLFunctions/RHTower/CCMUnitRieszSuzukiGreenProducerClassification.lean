import GaloisForLFunctions.RHTower.CCMUnitRieszResolventRHCriterion
import GaloisForLFunctions.RHTower.CCMGuinandWeilXiScrewGreenConnection
import GaloisForLFunctions.RHTower.SuzukiScrewBoundednessCriterion
import GaloisForLFunctions.RHTower.SuzukiScrewSmoothTestCriterion

/-!
# Suzuki–unit-Riesz Green producer classification

The literal completed outgoing unit-Riesz charge is the finite-window Green functional of
Suzuki's multiplicity-exact Xi screw, plus explicit polar and archimedean corrections.  The
Green kernel has uniformly bounded second-derivative mass; the polar main term cancels exactly;
and the archimedean remainder is uniformly bounded.  Suzuki boundedness therefore gives the
reverse implication missing from the unit-Riesz criterion.

Consequently RH is equivalent to each of: uniform boundedness of the critical unit-Riesz
resolvent, uniform boundedness on integer logarithms, and uniform total outgoing Hankel energy.
All statements are unconditional equivalences in the project foundations.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

def unitRieszSuzukiReporter (H h : ℝ) : ℝ :=
  Real.exp ((h - H) / 2) - Real.exp (h - H)

def unitRieszSuzukiReporterDeriv (H h : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp ((h - H) / 2) - Real.exp (h - H)

def unitRieszSuzukiReporterSecond (H h : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp ((h - H) / 2) - Real.exp (h - H)

theorem unitRieszSuzukiReporter_H (H : ℝ) : unitRieszSuzukiReporter H H = 0 := by
  simp [unitRieszSuzukiReporter]

theorem unitRieszSuzukiReporterDeriv_H (H : ℝ) : unitRieszSuzukiReporterDeriv H H = -(1 / 2 : ℝ) := by
  norm_num [unitRieszSuzukiReporterDeriv]

theorem hasDerivAt_unitRieszSuzukiReporter (H h : ℝ) :
    HasDerivAt (unitRieszSuzukiReporter H) (unitRieszSuzukiReporterDeriv H h) h := by
  have hshift : HasDerivAt (fun x : ℝ => x - H) 1 h :=
    (hasDerivAt_id h).sub_const H
  have hraw := ((Real.hasDerivAt_exp ((h - H) / 2)).comp h
      (hshift.div_const 2)).sub
    ((Real.hasDerivAt_exp (h - H)).comp h hshift)
  unfold unitRieszSuzukiReporter unitRieszSuzukiReporterDeriv
  convert hraw using 1
  all_goals first | rfl | ring_nf

theorem hasDerivAt_unitRieszSuzukiReporterDeriv (H h : ℝ) :
    HasDerivAt (unitRieszSuzukiReporterDeriv H) (unitRieszSuzukiReporterSecond H h) h := by
  have hshift : HasDerivAt (fun x : ℝ => x - H) 1 h :=
    (hasDerivAt_id h).sub_const H
  have hraw := (((Real.hasDerivAt_exp ((h - H) / 2)).comp h
      (hshift.div_const 2)).const_mul (1 / 2 : ℝ)).sub
    ((Real.hasDerivAt_exp (h - H)).comp h hshift)
  unfold unitRieszSuzukiReporterDeriv unitRieszSuzukiReporterSecond
  convert hraw using 1
  all_goals first | rfl | ring_nf

theorem unitRieszSuzuki_prime_term {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    criticalMellinAtomWeight k * unitRieszSuzukiReporter (Real.log N) (Real.log k) =
      (ArithmeticFunction.vonMangoldt k / Real.sqrt N) *
        (1 - Real.exp (-(Real.log N - Real.log k) / 2)) := by
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hsN : Real.sqrt (N : ℝ) = Real.exp (Real.log N / 2) :=
    sqrt_eq_exp_log_div_two hNR
  have hsk : Real.sqrt (k : ℝ) = Real.exp (Real.log k / 2) :=
    sqrt_eq_exp_log_div_two hkR
  rw [criticalMellinAtomWeight_eq_screwPrimeWeight hk, screwPrimeWeight, hsN, hsk]
  unfold unitRieszSuzukiReporter
  have hE1 : Real.exp ((Real.log k - Real.log N) / 2) =
      Real.exp (Real.log k / 2) / Real.exp (Real.log N / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hE2 : Real.exp (Real.log k - Real.log N) =
      Real.exp (Real.log k) / Real.exp (Real.log N) := by
    rw [← Real.exp_sub]
  have hneg : -(Real.log N - Real.log k) / 2 =
      (Real.log k - Real.log N) / 2 := by ring
  rw [hneg, hE1, hE2, Real.exp_log hNR, Real.exp_log hkR, ← hsN, ← hsk]
  have hsN0 : Real.sqrt (N : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hNR)
  have hsk0 : Real.sqrt (k : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hkR)
  field_simp [hsN0, hsk0]
  linear_combination
    -(ArithmeticFunction.vonMangoldt k * (k : ℝ)) * Real.sq_sqrt hNR.le +
      (ArithmeticFunction.vonMangoldt k * (N : ℝ)) * Real.sq_sqrt hkR.le

theorem unitRieszSuzuki_prime_sum {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ Finset.Icc 2 N,
      criticalMellinAtomWeight k * unitRieszSuzukiReporter (Real.log N) (Real.log k)) =
      unitRieszCoherentPrimeOutgoingCharge N := by
  rw [unitRieszCoherentPrimeOutgoingCharge]
  apply Finset.sum_congr rfl
  intro k hk
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_two hN
  have hk0 : 0 < k := lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hk).1
  exact unitRieszSuzuki_prime_term hN0 hk0

def unitRieszSuzukiBase : ℝ := 1 / 2

theorem unitRieszSuzukiBase_pos : 0 < unitRieszSuzukiBase := by norm_num [unitRieszSuzukiBase]

theorem unitRieszSuzukiBase_lt_log_two : unitRieszSuzukiBase < Real.log 2 := by
  unfold unitRieszSuzukiBase
  exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9

theorem unitRieszSuzukiBase_lt_log_of_two_le {k : ℕ} (hk : 2 ≤ k) :
    unitRieszSuzukiBase < Real.log k := by
  refine unitRieszSuzukiBase_lt_log_two.trans_le ?_
  exact Real.strictMonoOn_log.monotoneOn (by norm_num)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hk) : (0 : ℝ) < k)
    (by exact_mod_cast hk)

theorem continuous_unitRieszSuzukiReporterSecond (H : ℝ) : Continuous (unitRieszSuzukiReporterSecond H) := by
  unfold unitRieszSuzukiReporterSecond
  fun_prop

theorem unitRieszSuzuki_completedSource_log_nat {N : ℕ} (hN : 2 ≤ N) :
    ccmGuinandWeilCompletedSourceWindow unitRieszSuzukiBase (Real.log N)
      (unitRieszSuzukiReporter (Real.log N)) =
      unitRieszCoherentPrimeOutgoingCharge N +
        ∫ h in unitRieszSuzukiBase..Real.log N,
          unitRieszSuzukiReporter (Real.log N) h *
            (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2)) := by
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hfloor : ⌊Real.exp (Real.log N)⌋₊ = N := by
    rw [Real.exp_log hNR, Nat.floor_natCast]
  rw [ccmGuinandWeilCompletedSourceWindow, hfloor]
  congr 1
  rw [← unitRieszSuzuki_prime_sum hN]
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (unitRieszSuzukiBase_lt_log_of_two_le (Finset.mem_Icc.mp hk).1)]

def unitRieszSuzukiGreen (H : ℝ) : ℝ :=
  unitRieszSuzukiReporterDeriv H H * ccmGuinandWeilXiScrewCodiagonal unitRieszSuzukiBase H -
    ∫ h in unitRieszSuzukiBase..H,
      ccmGuinandWeilXiScrewCodiagonal unitRieszSuzukiBase h * unitRieszSuzukiReporterSecond H h

def unitRieszSuzukiPolarCorrection (H : ℝ) : ℝ :=
  (∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporter H h * (2 * Real.cosh (h / 2))) -
    Real.exp (H / 2) / 3

def unitRieszSuzukiArchCorrection (H : ℝ) : ℝ :=
  ∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h

def unitRieszSuzukiSecondMajorant (H h : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp ((h - H) / 2) + Real.exp (h - H)

def unitRieszSuzukiSecondMajorantPrimitive (H h : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.exp ((h - H) / 2) + Real.exp (h - H)

theorem hasDerivAt_unitRieszSuzukiSecondMajorantPrimitive (H h : ℝ) :
    HasDerivAt (unitRieszSuzukiSecondMajorantPrimitive H) (unitRieszSuzukiSecondMajorant H h) h := by
  have hshift : HasDerivAt (fun x : ℝ => x - H) 1 h :=
    (hasDerivAt_id h).sub_const H
  have hraw := (((Real.hasDerivAt_exp ((h - H) / 2)).comp h
      (hshift.div_const 2)).const_mul (1 / 2 : ℝ)).fun_add
    ((Real.hasDerivAt_exp (h - H)).comp h hshift)
  unfold unitRieszSuzukiSecondMajorantPrimitive unitRieszSuzukiSecondMajorant
  convert hraw using 1
  all_goals first | rfl | ring_nf

theorem integral_unitRieszSuzukiReporterSecond (H : ℝ) :
    (∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporterSecond H h) =
      unitRieszSuzukiReporterDeriv H H - unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h _hh => hasDerivAt_unitRieszSuzukiReporterDeriv H h)
    ((continuous_unitRieszSuzukiReporterSecond H).intervalIntegrable _ _)

theorem integral_sub_base_mul_unitRieszSuzukiReporterSecond
    {H : ℝ} (_hH : unitRieszSuzukiBase ≤ H) :
    (∫ h in unitRieszSuzukiBase..H, (h - unitRieszSuzukiBase) * unitRieszSuzukiReporterSecond H h) =
      (H - unitRieszSuzukiBase) * unitRieszSuzukiReporterDeriv H H -
        (unitRieszSuzukiReporter H H - unitRieszSuzukiReporter H unitRieszSuzukiBase) := by
  have hDint : IntervalIntegrable (unitRieszSuzukiReporterDeriv H) volume unitRieszSuzukiBase H := by
    exact (by
      unfold unitRieszSuzukiReporterDeriv
      fun_prop : Continuous (unitRieszSuzukiReporterDeriv H)).intervalIntegrable _ _
  have hSint : IntervalIntegrable (unitRieszSuzukiReporterSecond H) volume unitRieszSuzukiBase H :=
    (continuous_unitRieszSuzukiReporterSecond H).intervalIntegrable _ _
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun h : ℝ => h - unitRieszSuzukiBase) (u' := fun _ => 1)
    (v := unitRieszSuzukiReporterDeriv H) (v' := unitRieszSuzukiReporterSecond H)
    (fun h _hh => (hasDerivAt_id h).sub_const unitRieszSuzukiBase)
    (fun h _hh => hasDerivAt_unitRieszSuzukiReporterDeriv H h)
    (continuous_const.intervalIntegrable _ _) hSint
  have hFTC : (∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporterDeriv H h) =
      unitRieszSuzukiReporter H H - unitRieszSuzukiReporter H unitRieszSuzukiBase := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun h _hh => hasDerivAt_unitRieszSuzukiReporter H h) hDint
  simp only [one_mul] at hip
  rw [hFTC] at hip
  simpa only [sub_self, zero_mul, sub_zero] using hip

theorem unitRieszSuzukiGreen_eq_raw {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    unitRieszSuzukiGreen H =
      unitRieszSuzukiReporterDeriv H H * suzukiPsi H -
        (∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h) -
          suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase +
            ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase := by
  have hPsiInt : IntervalIntegrable
      (fun h => suzukiPsi h * unitRieszSuzukiReporterSecond H h) volume unitRieszSuzukiBase H :=
    (continuous_suzukiPsi.mul (continuous_unitRieszSuzukiReporterSecond H)).intervalIntegrable _ _
  have hSInt : IntervalIntegrable (unitRieszSuzukiReporterSecond H) volume unitRieszSuzukiBase H :=
    (continuous_unitRieszSuzukiReporterSecond H).intervalIntegrable _ _
  have hlinInt : IntervalIntegrable
      (fun h => (h - unitRieszSuzukiBase) * unitRieszSuzukiReporterSecond H h) volume unitRieszSuzukiBase H :=
    ((continuous_id.sub continuous_const).mul
      (continuous_unitRieszSuzukiReporterSecond H)).intervalIntegrable _ _
  have hCint :
      (∫ h in unitRieszSuzukiBase..H,
        ccmGuinandWeilXiScrewCodiagonal unitRieszSuzukiBase h * unitRieszSuzukiReporterSecond H h) =
      (∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h) -
        suzukiPsi unitRieszSuzukiBase * (∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporterSecond H h) -
          ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
            (∫ h in unitRieszSuzukiBase..H, (h - unitRieszSuzukiBase) * unitRieszSuzukiReporterSecond H h) := by
    rw [show (fun h : ℝ =>
      ccmGuinandWeilXiScrewCodiagonal unitRieszSuzukiBase h * unitRieszSuzukiReporterSecond H h) =
      fun h => suzukiPsi h * unitRieszSuzukiReporterSecond H h -
        suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterSecond H h -
          ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
            ((h - unitRieszSuzukiBase) * unitRieszSuzukiReporterSecond H h) by
      funext h
      rw [ccmGuinandWeilXiScrewCodiagonal]
      ring]
    rw [intervalIntegral.integral_sub
      (hPsiInt.sub (hSInt.const_mul (suzukiPsi unitRieszSuzukiBase)))
      (hlinInt.const_mul (ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase)),
      intervalIntegral.integral_sub hPsiInt (hSInt.const_mul (suzukiPsi unitRieszSuzukiBase)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [unitRieszSuzukiGreen, ccmGuinandWeilXiScrewCodiagonal, hCint,
    integral_unitRieszSuzukiReporterSecond,
    integral_sub_base_mul_unitRieszSuzukiReporterSecond hH,
    unitRieszSuzukiReporter_H]
  ring

theorem integral_unitRieszSuzukiSecondMajorant {H : ℝ} :
    (∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiSecondMajorant H h) =
      unitRieszSuzukiSecondMajorantPrimitive H H - unitRieszSuzukiSecondMajorantPrimitive H unitRieszSuzukiBase := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h _hh => hasDerivAt_unitRieszSuzukiSecondMajorantPrimitive H h)
    ((by unfold unitRieszSuzukiSecondMajorant; fun_prop : Continuous (unitRieszSuzukiSecondMajorant H)).intervalIntegrable _ _)

theorem abs_integral_suzukiPsi_mul_unitRieszSuzukiReporterSecond_le
    {C H : ℝ} (hC : 0 ≤ C)
    (hPsi : ∀ h : ℝ, 0 ≤ h → |suzukiPsi h| ≤ C)
    (hH : unitRieszSuzukiBase ≤ H) :
    |∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h| ≤ (3 / 2) * C := by
  let f : ℝ → ℝ := fun h => suzukiPsi h * unitRieszSuzukiReporterSecond H h
  let g : ℝ → ℝ := fun h => C * unitRieszSuzukiSecondMajorant H h
  have hf : Continuous f := continuous_suzukiPsi.mul (continuous_unitRieszSuzukiReporterSecond H)
  have hg : Continuous g := by
    dsimp only [g]
    unfold unitRieszSuzukiSecondMajorant
    fun_prop
  have hpoint : ∀ h ∈ Set.Icc unitRieszSuzukiBase H, ‖f h‖ ≤ g h := by
    intro h hh
    have hhalf0 : 0 ≤ (1 / 4 : ℝ) * Real.exp ((h - H) / 2) := by positivity
    have hone0 : 0 ≤ Real.exp (h - H) := (Real.exp_pos _).le
    have hsecond : |unitRieszSuzukiReporterSecond H h| ≤ unitRieszSuzukiSecondMajorant H h := by
      rw [unitRieszSuzukiReporterSecond, unitRieszSuzukiSecondMajorant]
      exact abs_sub _ _ |>.trans (by
        rw [abs_of_nonneg hhalf0, abs_of_nonneg hone0])
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hPsi h (unitRieszSuzukiBase_pos.le.trans hh.1)) hsecond
      (abs_nonneg _) hC
  calc
    |∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h| =
        ‖∫ h in unitRieszSuzukiBase..H, f h‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ h in unitRieszSuzukiBase..H, ‖f h‖ :=
      intervalIntegral.norm_integral_le_integral_norm hH
    _ ≤ ∫ h in unitRieszSuzukiBase..H, g h := by
      exact intervalIntegral.integral_mono_on hH (hf.norm.intervalIntegrable _ _)
        (hg.intervalIntegrable _ _) hpoint
    _ = C * (unitRieszSuzukiSecondMajorantPrimitive H H -
        unitRieszSuzukiSecondMajorantPrimitive H unitRieszSuzukiBase) := by
      rw [show (fun h : ℝ => g h) = fun h => C * unitRieszSuzukiSecondMajorant H h from rfl,
        intervalIntegral.integral_const_mul, integral_unitRieszSuzukiSecondMajorant]
    _ ≤ (3 / 2) * C := by
      have hprim0 : 0 ≤ unitRieszSuzukiSecondMajorantPrimitive H unitRieszSuzukiBase := by
        unfold unitRieszSuzukiSecondMajorantPrimitive
        positivity
      have hprimH : unitRieszSuzukiSecondMajorantPrimitive H H = 3 / 2 := by
        norm_num [unitRieszSuzukiSecondMajorantPrimitive]
      rw [hprimH]
      nlinarith

theorem abs_unitRieszSuzukiReporter_base_le_two {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiReporter H unitRieszSuzukiBase| ≤ 2 := by
  have hehalf : Real.exp ((unitRieszSuzukiBase - H) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have heone : Real.exp (unitRieszSuzukiBase - H) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [unitRieszSuzukiReporter]
  exact (abs_sub _ _).trans (by
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    linarith)

theorem abs_unitRieszSuzukiReporterDeriv_base_le_three_halves {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase| ≤ 3 / 2 := by
  have hehalf : Real.exp ((unitRieszSuzukiBase - H) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have heone : Real.exp (unitRieszSuzukiBase - H) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [unitRieszSuzukiReporterDeriv]
  exact (abs_sub _ _).trans (by
    rw [abs_of_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.exp ((unitRieszSuzukiBase - H) / 2)),
      abs_of_pos (Real.exp_pos _)]
    linarith)

theorem abs_unitRieszSuzukiGreen_le_of_suzuki_bound
    {C H : ℝ} (hC : 0 ≤ C)
    (hPsi : ∀ h : ℝ, 0 ≤ h → |suzukiPsi h| ≤ C)
    (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiGreen H| ≤ 4 * C +
      2 * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| := by
  have hraw := unitRieszSuzukiGreen_eq_raw hH
  have hHH : |unitRieszSuzukiReporterDeriv H H * suzukiPsi H| ≤ (1 / 2) * C := by
    rw [unitRieszSuzukiReporterDeriv_H, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hPsi H (unitRieszSuzukiBase_pos.le.trans hH)) (by norm_num)
  have hI := abs_integral_suzukiPsi_mul_unitRieszSuzukiReporterSecond_le hC hPsi hH
  have hbasePsi : |suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase| ≤
      C * (3 / 2) := by
    rw [abs_mul]
    exact mul_le_mul (hPsi unitRieszSuzukiBase unitRieszSuzukiBase_pos.le)
      (abs_unitRieszSuzukiReporterDeriv_base_le_three_halves hH) (abs_nonneg _) hC
  have hbaseSlope :
      |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase| ≤
        |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| * 2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_unitRieszSuzukiReporter_base_le_two hH) (abs_nonneg _)
  rw [hraw]
  calc
    |unitRieszSuzukiReporterDeriv H H * suzukiPsi H -
          (∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h) -
        suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase +
          ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase| ≤
        |unitRieszSuzukiReporterDeriv H H * suzukiPsi H| +
          |∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h| +
            |suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase| +
              |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase| := by
      calc
        |_ + _| ≤ |_ - _ - _| +
            |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase| := abs_add_le _ _
        _ ≤ (|_ - _| + |suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase|) +
            |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase| := by
          gcongr
          exact abs_sub _ _
        _ ≤ ((|unitRieszSuzukiReporterDeriv H H * suzukiPsi H| +
              |∫ h in unitRieszSuzukiBase..H, suzukiPsi h * unitRieszSuzukiReporterSecond H h|) +
              |suzukiPsi unitRieszSuzukiBase * unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase|) +
            |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase * unitRieszSuzukiReporter H unitRieszSuzukiBase| := by
          gcongr
          exact abs_sub _ _
        _ = _ := by ring
    _ ≤ 4 * C + 2 * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| := by
      nlinarith [hHH, hI, hbasePsi, hbaseSlope]

def unitRieszSuzukiPolarPrimitive (H h : ℝ) : ℝ :=
  Real.exp (-H / 2 + h) + h * Real.exp (-H / 2) -
    (2 / 3 : ℝ) * Real.exp (-H + 3 * h / 2) -
      2 * Real.exp (-H + h / 2)

theorem hasDerivAt_unitRieszSuzukiPolarPrimitive (H h : ℝ) :
    HasDerivAt (unitRieszSuzukiPolarPrimitive H)
      (unitRieszSuzukiReporter H h * (2 * Real.cosh (h / 2))) h := by
  have h1 : HasDerivAt (fun x : ℝ => Real.exp (-H / 2 + x))
      (Real.exp (-H / 2 + h)) h := by
    convert (Real.hasDerivAt_exp (-H / 2 + h)).comp h
      ((hasDerivAt_const h (-H / 2)).add (hasDerivAt_id h)) using 1
    all_goals first | rfl | ring_nf
  have h2 : HasDerivAt (fun x : ℝ => x * Real.exp (-H / 2))
      (Real.exp (-H / 2)) h := by
    convert (hasDerivAt_id h).mul_const (Real.exp (-H / 2)) using 1
    all_goals first | rfl | ring_nf
  have h3 : HasDerivAt (fun x : ℝ =>
      (2 / 3 : ℝ) * Real.exp (-H + 3 * x / 2))
      (Real.exp (-H + 3 * h / 2)) h := by
    have hi : HasDerivAt (fun x : ℝ => -H + 3 * x / 2) (3 / 2 : ℝ) h := by
      convert (hasDerivAt_const h (-H)).add
        (((hasDerivAt_id h).const_mul 3).div_const 2) using 1
      all_goals first | rfl | ring_nf
    convert ((Real.hasDerivAt_exp (-H + 3 * h / 2)).comp h hi).const_mul
      (2 / 3 : ℝ) using 1
    all_goals first | rfl | ring_nf
  have h4 : HasDerivAt (fun x : ℝ => 2 * Real.exp (-H + x / 2))
      (Real.exp (-H + h / 2)) h := by
    have hi : HasDerivAt (fun x : ℝ => -H + x / 2) (1 / 2 : ℝ) h := by
      convert (hasDerivAt_const h (-H)).add ((hasDerivAt_id h).div_const 2) using 1
      all_goals first | rfl | ring_nf
    convert ((Real.hasDerivAt_exp (-H + h / 2)).comp h hi).const_mul 2 using 1
    all_goals first | rfl | ring_nf
  have hraw := (h1.fun_add h2).fun_sub h3 |>.fun_sub h4
  unfold unitRieszSuzukiPolarPrimitive unitRieszSuzukiReporter
  convert hraw using 1
  all_goals first
  | rfl
  | (rw [Real.cosh_eq]
     rw [show 2 * ((Real.exp (h / 2) + Real.exp (-(h / 2))) / 2) =
       Real.exp (h / 2) + Real.exp (-(h / 2)) by ring]
     rw [sub_mul, mul_add, mul_add, ← Real.exp_add, ← Real.exp_add,
       ← Real.exp_add, ← Real.exp_add]
     ring_nf)

theorem unitRieszSuzukiPolarCorrection_eq (H : ℝ) :
    unitRieszSuzukiPolarCorrection H =
      (H - unitRieszSuzukiBase - 2 - Real.exp unitRieszSuzukiBase) * Real.exp (-H / 2) +
        ((2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
          2 * Real.exp (unitRieszSuzukiBase / 2)) * Real.exp (-H) := by
  have hcont : Continuous (fun h : ℝ =>
      unitRieszSuzukiReporter H h * (2 * Real.cosh (h / 2))) := by
    unfold unitRieszSuzukiReporter
    fun_prop
  have hint : (∫ h in unitRieszSuzukiBase..H,
      unitRieszSuzukiReporter H h * (2 * Real.cosh (h / 2))) =
      unitRieszSuzukiPolarPrimitive H H - unitRieszSuzukiPolarPrimitive H unitRieszSuzukiBase := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun h _hh => hasDerivAt_unitRieszSuzukiPolarPrimitive H h) (hcont.intervalIntegrable _ _)
  rw [unitRieszSuzukiPolarCorrection, hint]
  simp only [unitRieszSuzukiPolarPrimitive]
  rw [show Real.exp (-H / 2 + H) = Real.exp (H / 2) by congr 1; ring,
    show Real.exp (-H + 3 * H / 2) = Real.exp (H / 2) by congr 1; ring,
    show Real.exp (-H + H / 2) = Real.exp (-H / 2) by congr 1; ring,
    show Real.exp (-H / 2 + unitRieszSuzukiBase) = Real.exp unitRieszSuzukiBase * Real.exp (-H / 2) by
      rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-H + 3 * unitRieszSuzukiBase / 2) =
        Real.exp (3 * unitRieszSuzukiBase / 2) * Real.exp (-H) by
      rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-H + unitRieszSuzukiBase / 2) =
        Real.exp (unitRieszSuzukiBase / 2) * Real.exp (-H) by
      rw [← Real.exp_add]; congr 1; ring]
  ring

theorem sub_base_mul_exp_neg_half_le {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    (H - unitRieszSuzukiBase) * Real.exp (-H / 2) ≤ 2 * Real.exp (-unitRieszSuzukiBase / 2) := by
  have hx0 : 0 ≤ (H - unitRieszSuzukiBase) / 2 := by linarith
  have hexp := Real.add_one_le_exp ((H - unitRieszSuzukiBase) / 2)
  have hx : H - unitRieszSuzukiBase ≤ 2 * Real.exp ((H - unitRieszSuzukiBase) / 2) := by
    nlinarith
  calc
    (H - unitRieszSuzukiBase) * Real.exp (-H / 2) ≤
        (2 * Real.exp ((H - unitRieszSuzukiBase) / 2)) * Real.exp (-H / 2) := by
      exact mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = 2 * Real.exp (-unitRieszSuzukiBase / 2) := by
      rw [show 2 * Real.exp ((H - unitRieszSuzukiBase) / 2) * Real.exp (-H / 2) =
        2 * (Real.exp ((H - unitRieszSuzukiBase) / 2) * Real.exp (-H / 2)) by ring,
        ← Real.exp_add]
      congr 2
      ring

def unitRieszSuzukiPolarUniformBound : ℝ :=
  2 * Real.exp (-unitRieszSuzukiBase / 2) +
    (2 + Real.exp unitRieszSuzukiBase) * Real.exp (-unitRieszSuzukiBase / 2) +
      ((2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
        2 * Real.exp (unitRieszSuzukiBase / 2)) * Real.exp (-unitRieszSuzukiBase)

theorem abs_unitRieszSuzukiPolarCorrection_le {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiPolarCorrection H| ≤ unitRieszSuzukiPolarUniformBound := by
  have hehalf : Real.exp (-H / 2) ≤ Real.exp (-unitRieszSuzukiBase / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have heone : Real.exp (-H) ≤ Real.exp (-unitRieszSuzukiBase) :=
    Real.exp_le_exp.mpr (by linarith)
  have hx0 : 0 ≤ H - unitRieszSuzukiBase := sub_nonneg.mpr hH
  have hc0 : 0 ≤ 2 + Real.exp unitRieszSuzukiBase := by positivity
  have hcoef0 : 0 ≤ (2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
      2 * Real.exp (unitRieszSuzukiBase / 2) := by positivity
  rw [unitRieszSuzukiPolarCorrection_eq]
  calc
    |_ + _| ≤ |(H - unitRieszSuzukiBase - 2 - Real.exp unitRieszSuzukiBase) * Real.exp (-H / 2)| +
        |((2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
          2 * Real.exp (unitRieszSuzukiBase / 2)) * Real.exp (-H)| := abs_add_le _ _
    _ ≤ ((H - unitRieszSuzukiBase) + (2 + Real.exp unitRieszSuzukiBase)) * Real.exp (-H / 2) +
        ((2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
          2 * Real.exp (unitRieszSuzukiBase / 2)) * Real.exp (-H) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
        abs_of_nonneg hcoef0]
      gcongr
      rw [show H - unitRieszSuzukiBase - 2 - Real.exp unitRieszSuzukiBase =
        (H - unitRieszSuzukiBase) - (2 + Real.exp unitRieszSuzukiBase) by ring]
      calc
        |(H - unitRieszSuzukiBase) - (2 + Real.exp unitRieszSuzukiBase)| ≤
            |H - unitRieszSuzukiBase| + |2 + Real.exp unitRieszSuzukiBase| := abs_sub _ _
        _ = (H - unitRieszSuzukiBase) + (2 + Real.exp unitRieszSuzukiBase) := by
          rw [abs_of_nonneg hx0, abs_of_nonneg hc0]
    _ = (H - unitRieszSuzukiBase) * Real.exp (-H / 2) +
          (2 + Real.exp unitRieszSuzukiBase) * Real.exp (-H / 2) +
        ((2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
          2 * Real.exp (unitRieszSuzukiBase / 2)) * Real.exp (-H) := by ring
    _ ≤ unitRieszSuzukiPolarUniformBound := by
      rw [unitRieszSuzukiPolarUniformBound]
      exact add_le_add
        (add_le_add (sub_base_mul_exp_neg_half_le hH)
          (mul_le_mul_of_nonneg_left hehalf hc0))
        (mul_le_mul_of_nonneg_left heone hcoef0)

def unitRieszSuzukiArchDenominator : ℝ := 1 - Real.exp (-2 * unitRieszSuzukiBase)

theorem unitRieszSuzukiArchDenominator_pos : 0 < unitRieszSuzukiArchDenominator := by
  unfold unitRieszSuzukiArchDenominator
  have hneg : -2 * unitRieszSuzukiBase < 0 := by nlinarith [unitRieszSuzukiBase_pos]
  have he := Real.exp_lt_one_iff.mpr hneg
  linarith

theorem unitRieszSuzukiReporter_nonneg_of_mem
    {H h : ℝ} (hh : h ≤ H) : 0 ≤ unitRieszSuzukiReporter H h := by
  rw [unitRieszSuzukiReporter]
  have hx : h - H ≤ (h - H) / 2 := by linarith
  exact sub_nonneg.mpr (Real.exp_le_exp.mpr hx)

theorem abs_unitRieszSuzukiReporter_le_exp_half
    {H h : ℝ} (hh : h ≤ H) :
    |unitRieszSuzukiReporter H h| ≤ Real.exp ((h - H) / 2) := by
  rw [abs_of_nonneg (unitRieszSuzukiReporter_nonneg_of_mem hh), unitRieszSuzukiReporter]
  linarith [Real.exp_pos (h - H)]

theorem ccmPublishedArchimedeanDensity_le_unitRieszSuzukiBase
    {h : ℝ} (hh : unitRieszSuzukiBase ≤ h) :
    ccmPublishedArchimedeanDensity h ≤ Real.exp (-h / 2) / unitRieszSuzukiArchDenominator := by
  have hhpos : 0 < h := unitRieszSuzukiBase_pos.trans_le hh
  have hdpos : 0 < 1 - Real.exp (-2 * h) := by
    have he : Real.exp (-2 * h) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hden : unitRieszSuzukiArchDenominator ≤ 1 - Real.exp (-2 * h) := by
    unfold unitRieszSuzukiArchDenominator
    have he := Real.exp_le_exp.mpr (show -2 * h ≤ -2 * unitRieszSuzukiBase by linarith)
    linarith
  rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hhpos]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le unitRieszSuzukiArchDenominator_pos hden

def unitRieszSuzukiArchUniformBound : ℝ :=
  2 * Real.exp (-unitRieszSuzukiBase / 2) / unitRieszSuzukiArchDenominator

theorem abs_unitRieszSuzukiArchCorrection_le {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiArchCorrection H| ≤ unitRieszSuzukiArchUniformBound := by
  have hpoint : ∀ h ∈ Set.uIoc unitRieszSuzukiBase H,
      ‖unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h‖ ≤
        Real.exp (-H / 2) / unitRieszSuzukiArchDenominator := by
    intro h hh
    rw [Set.uIoc_of_le hH] at hh
    have hrep0 := unitRieszSuzukiReporter_nonneg_of_mem hh.2
    have hden0 : 0 ≤ ccmPublishedArchimedeanDensity h := by
      rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div
        (unitRieszSuzukiBase_pos.trans hh.1)]
      exact div_nonneg (Real.exp_pos _).le (by
        have he : Real.exp (-2 * h) < 1 := by
          rw [Real.exp_lt_one_iff]
          nlinarith [unitRieszSuzukiBase_pos.trans hh.1]
        linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrep0 hden0)]
    calc
      unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h ≤
          Real.exp ((h - H) / 2) *
            (Real.exp (-h / 2) / unitRieszSuzukiArchDenominator) := by
        exact mul_le_mul ((le_abs_self _).trans (abs_unitRieszSuzukiReporter_le_exp_half hh.2))
          (ccmPublishedArchimedeanDensity_le_unitRieszSuzukiBase hh.1.le) hden0
          (Real.exp_pos _).le
      _ = Real.exp (-H / 2) / unitRieszSuzukiArchDenominator := by
        rw [show Real.exp ((h - H) / 2) *
            (Real.exp (-h / 2) / unitRieszSuzukiArchDenominator) =
          (Real.exp ((h - H) / 2) * Real.exp (-h / 2)) /
            unitRieszSuzukiArchDenominator by ring,
          ← Real.exp_add]
        congr 2
        ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := unitRieszSuzukiBase) (b := H)
    (C := Real.exp (-H / 2) / unitRieszSuzukiArchDenominator)
    (f := fun h => unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h) hpoint
  have hb' : |unitRieszSuzukiArchCorrection H| ≤
      (Real.exp (-H / 2) / unitRieszSuzukiArchDenominator) * |H - unitRieszSuzukiBase| := by
    rw [unitRieszSuzukiArchCorrection, ← Real.norm_eq_abs]
    exact hb
  calc
    |unitRieszSuzukiArchCorrection H| ≤
        (Real.exp (-H / 2) / unitRieszSuzukiArchDenominator) * |H - unitRieszSuzukiBase| := hb'
    _ = ((H - unitRieszSuzukiBase) * Real.exp (-H / 2)) / unitRieszSuzukiArchDenominator := by
      rw [abs_of_nonneg (sub_nonneg.mpr hH)]
      ring
    _ ≤ unitRieszSuzukiArchUniformBound := by
      rw [unitRieszSuzukiArchUniformBound]
      exact div_le_div_of_nonneg_right (sub_base_mul_exp_neg_half_le hH)
        unitRieszSuzukiArchDenominator_pos.le



theorem unitRieszSuzuki_completedSource_eq_green {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    ccmGuinandWeilCompletedSourceWindow unitRieszSuzukiBase H (unitRieszSuzukiReporter H) = unitRieszSuzukiGreen H := by
  have hgreen := ccmGuinandWeilCompletedSourceWindow_eq_xiScrewGreen
    unitRieszSuzukiBase_pos hH
    (F := unitRieszSuzukiReporter H) (F' := unitRieszSuzukiReporterDeriv H) (F'' := unitRieszSuzukiReporterSecond H)
    (fun x _hx => hasDerivAt_unitRieszSuzukiReporter H x)
    (fun x _hx => hasDerivAt_unitRieszSuzukiReporterDeriv H x)
    (continuous_unitRieszSuzukiReporterSecond H).continuousOn
  simpa only [unitRieszSuzukiReporter_H, neg_zero, zero_mul, zero_add, unitRieszSuzukiGreen] using hgreen

theorem unitRieszSuzuki_outgoing_eq_green {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentCompletedOutgoingCharge N =
      unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N) -
        unitRieszSuzukiArchCorrection (Real.log N) := by
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log N / 2) :=
    sqrt_eq_exp_log_div_two hNR
  have hH : unitRieszSuzukiBase ≤ Real.log N := by
    exact (unitRieszSuzukiBase_lt_log_two.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hNR
        (by exact_mod_cast hN))).le
  have hsource := unitRieszSuzuki_completedSource_log_nat hN
  rw [unitRieszSuzuki_completedSource_eq_green hH] at hsource
  have hreporter : Continuous (unitRieszSuzukiReporter (Real.log N)) := by
    unfold unitRieszSuzukiReporter
    fun_prop
  have harchDensity : ContinuousOn ccmPublishedArchimedeanDensity
      (Set.Icc unitRieszSuzukiBase (Real.log N)) := by
    intro h hh
    have hhpos : 0 < h := unitRieszSuzukiBase_pos.trans_le hh.1
    unfold ccmPublishedArchimedeanDensity
    have hden : Real.exp h - Real.exp (-h) ≠ 0 := by
      have he : Real.exp (-h) < Real.exp h := Real.exp_lt_exp.mpr (by linarith)
      linarith
    exact ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousAt.div
      ((Real.continuous_exp.sub
        (Real.continuous_exp.comp continuous_id.neg)).continuousAt) hden).continuousWithinAt
  have harchInt : IntervalIntegrable
      (fun h => unitRieszSuzukiReporter (Real.log N) h * ccmPublishedArchimedeanDensity h)
      volume unitRieszSuzukiBase (Real.log N) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hH]
    exact hreporter.continuousOn.mul harchDensity
  have hpolarInt : IntervalIntegrable
      (fun h => unitRieszSuzukiReporter (Real.log N) h * (2 * Real.cosh (h / 2)))
      volume unitRieszSuzukiBase (Real.log N) := by
    exact (hreporter.mul (continuous_const.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
  have hsplit :
      (∫ h in unitRieszSuzukiBase..Real.log N,
        unitRieszSuzukiReporter (Real.log N) h *
          (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2))) =
      (∫ h in unitRieszSuzukiBase..Real.log N,
        unitRieszSuzukiReporter (Real.log N) h * ccmPublishedArchimedeanDensity h) -
      ∫ h in unitRieszSuzukiBase..Real.log N,
        unitRieszSuzukiReporter (Real.log N) h * (2 * Real.cosh (h / 2)) := by
    rw [← intervalIntegral.integral_sub harchInt hpolarInt]
    apply intervalIntegral.integral_congr
    intro h _hh
    ring
  rw [hsplit] at hsource
  rw [unitRieszCoherentCompletedOutgoingCharge,
    unitRieszCoherentPolarOutgoingCharge_eq, hsqrt,
    unitRieszSuzukiPolarCorrection, unitRieszSuzukiArchCorrection]
  linarith [hsource]

end RHTower

namespace RHTower

open GaloisForLFunctions.RHTower

theorem exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ N : ℕ, 2 ≤ N →
      |criticalMellinChebyshevResolventSource (Real.log N)| ≤ B₀ := by
  obtain ⟨C, hPsi⟩ := riemannHypothesis_iff_suzukiExplicitScrewBounded.mp hRH
  have hC : 0 ≤ C :=
    (abs_nonneg (suzukiPsi 0)).trans (hPsi 0 (le_refl 0))
  let BG : ℝ := 4 * C + 2 * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase|
  let BQ : ℝ := BG + unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound
  let B₀ : ℝ := 2 * BQ
  have hBG : 0 ≤ BG := by
    dsimp only [BG]
    positivity
  have hPolar0 : 0 ≤ unitRieszSuzukiPolarUniformBound := by
    unfold unitRieszSuzukiPolarUniformBound
    positivity
  have hArch0 : 0 ≤ unitRieszSuzukiArchUniformBound := by
    unfold unitRieszSuzukiArchUniformBound
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      unitRieszSuzukiArchDenominator_pos.le
  have hBQ : 0 ≤ BQ := by dsimp only [BQ]; positivity
  refine ⟨B₀, by dsimp only [B₀]; positivity, ?_⟩
  intro N hN
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hH : unitRieszSuzukiBase ≤ Real.log N := by
    exact (unitRieszSuzukiBase_lt_log_two.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num) hNR
        (by exact_mod_cast hN))).le
  have hG := abs_unitRieszSuzukiGreen_le_of_suzuki_bound hC hPsi hH
  have hP := abs_unitRieszSuzukiPolarCorrection_le hH
  have hA := abs_unitRieszSuzukiArchCorrection_le hH
  have hout := unitRieszSuzuki_outgoing_eq_green hN
  have hq : |unitRieszCoherentCompletedOutgoingCharge N| ≤ BQ := by
    rw [hout]
    calc
      |unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N) -
          unitRieszSuzukiArchCorrection (Real.log N)| ≤
          |unitRieszSuzukiGreen (Real.log N)| + |unitRieszSuzukiPolarCorrection (Real.log N)| +
            |unitRieszSuzukiArchCorrection (Real.log N)| := by
        have hsub := abs_sub
          (unitRieszSuzukiGreen (Real.log N) + unitRieszSuzukiPolarCorrection (Real.log N))
          (unitRieszSuzukiArchCorrection (Real.log N))
        have hadd := abs_add_le (unitRieszSuzukiGreen (Real.log N))
          (unitRieszSuzukiPolarCorrection (Real.log N))
        linarith
      _ ≤ BQ := by
        dsimp only [BQ, BG]
        linarith
  have hcharge := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN
  have hres :
      criticalMellinChebyshevResolventSource (Real.log N) =
        2 * unitRieszCoherentCompletedOutgoingCharge N := by
    linarith
  rw [hres, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hq (by norm_num)

def UnitRieszCriticalResolventBounded : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
    |criticalMellinChebyshevResolventSource t| ≤ B

def UnitRieszCriticalResolventLogNatBounded : Prop :=
  ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ N : ℕ, 2 ≤ N →
    |criticalMellinChebyshevResolventSource (Real.log N)| ≤ B₀

theorem riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded :
    RiemannHypothesis ↔ UnitRieszCriticalResolventLogNatBounded := by
  constructor
  · intro hRH
    exact exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis hRH
  · rintro ⟨B₀, _hB₀, hlog⟩
    exact riemannHypothesis_of_criticalMellinChebyshevResolventSource_log_nat_bound hlog

theorem riemannHypothesis_iff_unitRieszCriticalResolventBounded :
    RiemannHypothesis ↔ UnitRieszCriticalResolventBounded := by
  constructor
  · intro hRH
    obtain ⟨B₀, _hB₀, hlog⟩ :=
      exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis hRH
    exact exists_global_bound_criticalMellinChebyshevResolventSource_of_log_nat_bound hlog
  · rintro ⟨B, hB, hglobal⟩
    exact riemannHypothesis_of_bounded_criticalMellinChebyshevResolventSource hB hglobal

def UnitRieszCompletedOutgoingEnergyBounded : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ N : ℕ, 2 ≤ N →
    (∫ u in Set.Ioi (0 : ℝ),
      leakDensity (unitRieszCoherentCompletedOutgoingProfile N) u) ≤ E

theorem riemannHypothesis_iff_unitRieszCompletedOutgoingEnergyBounded :
    RiemannHypothesis ↔ UnitRieszCompletedOutgoingEnergyBounded := by
  constructor
  · intro hRH
    obtain ⟨B₀, hB₀, hlog⟩ :=
      exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis hRH
    refine ⟨B₀ ^ 2, sq_nonneg B₀, ?_⟩
    intro N hN
    rw [integral_leakDensity_unitRieszCoherentCompletedOutgoingProfile]
    rw [unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN]
    have hsquare := (sq_le_sq₀ (abs_nonneg _) hB₀).2 (hlog N hN)
    rw [sq_abs] at hsquare
    nlinarith
  · rintro ⟨E, hE, henergy⟩
    apply riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded.mpr
    refine ⟨4 * E + 1, by positivity, ?_⟩
    intro N hN
    have hbound := henergy N hN
    rw [integral_leakDensity_unitRieszCoherentCompletedOutgoingProfile,
      unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN] at hbound
    have habs : |criticalMellinChebyshevResolventSource (Real.log N)| ≤
        (criticalMellinChebyshevResolventSource (Real.log N)) ^ 2 + 1 := by
      have hs := sq_nonneg (|criticalMellinChebyshevResolventSource
        (Real.log N)| - 1 / 2)
      nlinarith [sq_abs (criticalMellinChebyshevResolventSource (Real.log N))]
    ring_nf at hbound
    nlinarith

end RHTower

