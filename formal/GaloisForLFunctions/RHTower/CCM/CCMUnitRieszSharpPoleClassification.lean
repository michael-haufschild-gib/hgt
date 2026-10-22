import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszSuzukiGreenProducerClassification
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFirstGap
import GaloisForLFunctions.HTGeometry.SummableSpectrumScrewValue

/-!
# Sharp CCM unit-Riesz pole classification

This module resolves the sharp constant left open by the outgoing unit-Riesz/HG weld.  Under RH,
the multiplicity-exact Xi reciprocal-square mass is the zeroth normalized prime--Gamma moment,
so Suzuki's entire relation hull is smaller than `58 / 625`.  At the forced Green base `1 / 2`,
the first Lerch atom and exact archimedean constants sharpen the right-slope bound to absolute
value `< 1`.  The reporter itself has the universal caps `|F| ≤ 1 / 4` and `|F'| ≤ 1 / 2`.

These facts give a Green contribution `< 241 / 500`.  Independent symbolic estimates bound both
the exact polar correction and exact archimedean correction by `7 / 10` on integer-log windows.
Thus every completed outgoing charge has absolute value `< 2` under RH.  The previously proved
reverse implication then yields the exact unconditional classification

`RH ↔ every literal completed outgoing CCM-HG profile is dominated by the pole packet`.

No numerical zero data, computation, added axiom, or asymptotic hypothesis occurs.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry
open HTGeometry

theorem tsum_xiCriticalScrewWeight_eq_normalizedPrimeArchMoment_zero_of_rh
    (hRH : RiemannHypothesis) :
    (∑' q : XiZeroCopy, xiCriticalScrewWeight q) = normalizedPrimeArchMoment 0 := by
  have hsum : Summable xiCriticalScrewWeight :=
    summable_xiCriticalScrewWeight_of_rh hRH
  have hterm : ∀ q : XiZeroCopy,
      ((xiCriticalScrewWeight q : ℝ) : ℂ) = xiZeroCopyReciprocalSquare q := by
    intro q
    rw [xiCriticalScrewWeight, xiZeroCopyReciprocalSquare,
      xiSpectralPoint_eq_ofReal_of_rh hRH q]
    norm_num [div_pow]
  have hsource := primeArchSourceMoment_eq_xiCentralReciprocalMoment 0
  change ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) = xiCentralReciprocalMoment 0 at hsource
  have hcomplex : (((∑' q : XiZeroCopy, xiCriticalScrewWeight q) : ℝ) : ℂ) =
      ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) := by
    calc
      (((∑' q : XiZeroCopy, xiCriticalScrewWeight q) : ℝ) : ℂ) =
          ∑' q : XiZeroCopy, ((xiCriticalScrewWeight q : ℝ) : ℂ) :=
        Complex.ofReal_tsum xiCriticalScrewWeight
      _ = ∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q := tsum_congr hterm
      _ = xiCentralReciprocalMoment 0 := by
        simpa using tsum_xiZeroCopyReciprocalSquare_pow 0
      _ = ((normalizedPrimeArchMoment 0 : ℝ) : ℂ) := hsource.symm
  exact_mod_cast hcomplex

theorem screwHullMax_lt_fiftyEight_over_sixHundredTwentyFive_of_rh
    (hRH : RiemannHypothesis) :
    screwHullMax xiCriticalScrewWeight xiRealSpectralPoint < 58 / 625 := by
  have hsum := summable_xiCriticalScrewWeight_of_rh hRH
  calc
    screwHullMax xiCriticalScrewWeight xiRealSpectralPoint ≤
        2 * ∑' q : XiZeroCopy, xiCriticalScrewWeight q :=
      screwHullMax_le_two_mul xiCriticalScrewWeight_nonneg hsum
    _ = 2 * normalizedPrimeArchMoment 0 := by
      rw [tsum_xiCriticalScrewWeight_eq_normalizedPrimeArchMoment_zero_of_rh hRH]
    _ < 58 / 625 := by
      nlinarith [normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive]

theorem criticalMellinPrimeMass_unitRieszSuzukiBase_eq_zero :
    criticalMellinPrimeMass unitRieszSuzukiBase = 0 := by
  rw [criticalMellinPrimeMass_eq_sum_Icc_two]
  have hfloor : ⌊Real.exp unitRieszSuzukiBase⌋₊ < 2 := by
    apply (Nat.floor_lt (Real.exp_pos _).le).2
    calc
      Real.exp unitRieszSuzukiBase < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr unitRieszSuzukiBase_lt_log_two
      _ = 2 := Real.exp_log (by norm_num)
  rw [Finset.Icc_eq_empty_of_lt hfloor]
  simp

theorem exp_unitRieszSuzukiBase_half_lt_thirteen_tenths :
    Real.exp (unitRieszSuzukiBase / 2) < 13 / 10 := by
  unfold unitRieszSuzukiBase
  norm_num only
  by_contra h
  have hle : (13 / 10 : ℝ) ≤ Real.exp (1 / 4) := le_of_not_gt h
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13 / 10) hle 4
  have heq : Real.exp (1 / 4 : ℝ) ^ (4 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [heq] at hp
  nlinarith [Real.exp_one_lt_d9]

theorem four_fifths_gt_exp_neg_unitRieszSuzukiBase_half :
    Real.exp (-(unitRieszSuzukiBase / 2)) < 4 / 5 := by
  have hq : unitRieszSuzukiBase / 2 = (1 / 4 : ℝ) := by
    norm_num [unitRieszSuzukiBase]
  rw [hq]
  have hlower : (5 / 4 : ℝ) < Real.exp (1 / 4) := by
    nlinarith [Real.add_one_lt_exp (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  have hprod : Real.exp (-(1 / 4 : ℝ)) * Real.exp (1 / 4) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos (-(1 / 4 : ℝ))]

theorem screwLinearCoeff_half_lt_neg_five_halves :
    screwLinearCoeff / 2 < -(5 / 2 : ℝ) := by
  have hlogpi : (1 : ℝ) < Real.log Real.pi := by
    rw [Real.lt_log_iff_exp_lt Real.pi_pos]
    exact Real.exp_one_lt_d9.trans (by nlinarith [Real.pi_gt_d2])
  rw [screwLinearCoeff_eq]
  nlinarith [Real.log_two_gt_d9, Real.one_half_lt_eulerMascheroniConstant,
    Real.pi_gt_d2]

theorem neg_screwLerchTail₁_unitRieszSuzukiBase_nonneg :
    0 ≤ -screwLerchTail₁ unitRieszSuzukiBase := by
  rw [neg_screwLerchTail₁_eq_tsum]
  exact tsum_nonneg fun k =>
    div_nonneg (Real.exp_pos _).le (lerchExp_pos k).le

theorem three_halves_lt_neg_screwLerchTail₁_unitRieszSuzukiBase :
    (3 / 2 : ℝ) < -screwLerchTail₁ unitRieszSuzukiBase := by
  have hsummable : Summable (fun k : ℕ =>
      Real.exp (-(lerchExp k * unitRieszSuzukiBase)) / lerchExp k) := by
    simpa only [summable_neg_iff] using
      (summable_screwLerchTerm₁ unitRieszSuzukiBase_pos)
  have hfirst : Real.exp (-(lerchExp 0 * unitRieszSuzukiBase)) / lerchExp 0 ≤
      ∑' k : ℕ, Real.exp (-(lerchExp k * unitRieszSuzukiBase)) / lerchExp k := by
    simpa only [Finset.sum_singleton] using hsummable.sum_le_tsum {0} (fun k _ =>
      div_nonneg (Real.exp_pos _).le (lerchExp_pos k).le)
  rw [← neg_screwLerchTail₁_eq_tsum] at hfirst
  have hnegExpLower : (3 / 4 : ℝ) < Real.exp (-(unitRieszSuzukiBase / 2)) := by
    norm_num [unitRieszSuzukiBase]
    nlinarith [Real.add_one_lt_exp (by norm_num : (-(1 / 4 : ℝ)) ≠ 0)]
  norm_num [lerchExp, unitRieszSuzukiBase] at hfirst
  norm_num [unitRieszSuzukiBase] at hnegExpLower
  ring_nf at hfirst
  change (3 / 2 : ℝ) < -screwLerchTail₁ (1 / 2)
  nlinarith

theorem neg_screwLerchTail₁_unitRieszSuzukiBase_lt_nineteen_tenths :
    -screwLerchTail₁ unitRieszSuzukiBase < 19 / 10 := by
  let y : ℝ := Real.exp (-(unitRieszSuzukiBase / 2))
  have hypos : 0 < y := Real.exp_pos _
  have hylt : y < 4 / 5 := by
    exact four_fifths_gt_exp_neg_unitRieszSuzukiBase_half
  have hyone : y < 1 := hylt.trans (by norm_num)
  have hratioPos : 0 < (1 + y) / (1 - y) :=
    div_pos (by positivity) (sub_pos.mpr hyone)
  have hratio : (1 + y) / (1 - y) < 9 := by
    rw [div_lt_iff₀ (sub_pos.mpr hyone)]
    nlinarith
  have hlog : Real.log ((1 + y) / (1 - y)) < 2 * Real.log 3 := by
    calc
      Real.log ((1 + y) / (1 - y)) < Real.log 9 :=
        Real.log_lt_log hratioPos hratio
      _ = 2 * Real.log 3 := by
        rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
        norm_num
  have hatan : Real.arctan y < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono hyone
  have hclosed := screwLerchTail₁_eq_suzukiLerchTailOneClosed
    unitRieszSuzukiBase_pos
  rw [hclosed]
  unfold suzukiLerchTailOneClosed
  rw [show -(-Real.arctan (Real.exp (-(unitRieszSuzukiBase / 2))) -
      (1 / 2 : ℝ) * Real.log
        ((1 + Real.exp (-(unitRieszSuzukiBase / 2))) /
          (1 - Real.exp (-(unitRieszSuzukiBase / 2))))) =
      Real.arctan (Real.exp (-(unitRieszSuzukiBase / 2))) +
        (1 / 2 : ℝ) * Real.log
          ((1 + Real.exp (-(unitRieszSuzukiBase / 2))) /
            (1 - Real.exp (-(unitRieszSuzukiBase / 2)))) by ring]
  change Real.arctan y + (1 / 2 : ℝ) *
      Real.log ((1 + y) / (1 - y)) < 19 / 10
  nlinarith [Real.pi_lt_d4, Real.log_three_lt_d9]

theorem abs_ccmGuinandWeilXiScrewRightSlope_unitRieszSuzukiBase_lt_two :
    |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| < 2 := by
  have hposExp : (5 / 4 : ℝ) < Real.exp (unitRieszSuzukiBase / 2) := by
    norm_num [unitRieszSuzukiBase]
    nlinarith [Real.add_one_lt_exp (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  have hnegExp := four_fifths_gt_exp_neg_unitRieszSuzukiBase_half
  have hlinearLower := neg_twentySeven_tenths_lt_screwLinearCoeff_half
  have hlinearUpper := screwLinearCoeff_half_lt_neg_five_halves
  have htail0 := neg_screwLerchTail₁_unitRieszSuzukiBase_nonneg
  have htailUpper := neg_screwLerchTail₁_unitRieszSuzukiBase_lt_nineteen_tenths
  have hposUpper := exp_unitRieszSuzukiBase_half_lt_thirteen_tenths
  have hnegExpPos : 0 < Real.exp (-(unitRieszSuzukiBase / 2)) := Real.exp_pos _
  rw [ccmGuinandWeilXiScrewRightSlope,
    criticalMellinPrimeMass_unitRieszSuzukiBase_eq_zero, sub_zero,
    ccmGuinandWeilXiScrewSmoothSlope]
  rw [abs_lt]
  constructor <;> nlinarith

theorem abs_ccmGuinandWeilXiScrewRightSlope_unitRieszSuzukiBase_lt_one :
    |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| < 1 := by
  have hposExp : (5 / 4 : ℝ) < Real.exp (unitRieszSuzukiBase / 2) := by
    norm_num [unitRieszSuzukiBase]
    nlinarith [Real.add_one_lt_exp (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  have hnegExpUpper := four_fifths_gt_exp_neg_unitRieszSuzukiBase_half
  have hnegExpLower : (3 / 4 : ℝ) < Real.exp (-(unitRieszSuzukiBase / 2)) := by
    norm_num [unitRieszSuzukiBase]
    nlinarith [Real.add_one_lt_exp (by norm_num : (-(1 / 4 : ℝ)) ≠ 0)]
  have hlinearLower := neg_twentySeven_tenths_lt_screwLinearCoeff_half
  have hlinearUpper := screwLinearCoeff_half_lt_neg_five_halves
  have htailLower := three_halves_lt_neg_screwLerchTail₁_unitRieszSuzukiBase
  have htailUpper := neg_screwLerchTail₁_unitRieszSuzukiBase_lt_nineteen_tenths
  have hposUpper := exp_unitRieszSuzukiBase_half_lt_thirteen_tenths
  rw [ccmGuinandWeilXiScrewRightSlope,
    criticalMellinPrimeMass_unitRieszSuzukiBase_eq_zero, sub_zero,
    ccmGuinandWeilXiScrewSmoothSlope, abs_lt]
  constructor <;> nlinarith

theorem abs_unitRieszSuzukiReporter_le_quarter
    {H h : ℝ} (hh : h ≤ H) :
    |unitRieszSuzukiReporter H h| ≤ 1 / 4 := by
  let x : ℝ := Real.exp ((h - H) / 2)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    rw [Real.exp_le_one_iff]
    linarith
  have hxpow : Real.exp (h - H) = x ^ (2 : ℕ) := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [abs_of_nonneg (unitRieszSuzukiReporter_nonneg_of_mem hh),
    unitRieszSuzukiReporter, hxpow]
  change x - x ^ (2 : ℕ) ≤ 1 / 4
  nlinarith [sq_nonneg (x - 1 / 2)]

theorem abs_unitRieszSuzukiReporterDeriv_le_half
    {H h : ℝ} (hh : h ≤ H) :
    |unitRieszSuzukiReporterDeriv H h| ≤ 1 / 2 := by
  let x : ℝ := Real.exp ((h - H) / 2)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := by
    dsimp only [x]
    rw [Real.exp_le_one_iff]
    linarith
  have hxpow : Real.exp (h - H) = x ^ (2 : ℕ) := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [unitRieszSuzukiReporterDeriv, hxpow, abs_le]
  change -(1 / 2 : ℝ) ≤ (1 / 2 : ℝ) * x - x ^ (2 : ℕ) ∧
    (1 / 2 : ℝ) * x - x ^ (2 : ℕ) ≤ 1 / 2
  constructor <;> nlinarith [mul_self_le_mul_self hx0 hx1]

theorem abs_suzukiPsi_lt_fiftyEight_over_sixHundredTwentyFive_of_rh
    (hRH : RiemannHypothesis) (h : ℝ) :
    |suzukiPsi h| < 58 / 625 := by
  rw [suzukiPsi_eq_xiCriticalScrewSeries_of_rh hRH h]
  have hsum := summable_xiCriticalScrewWeight_of_rh hRH
  have hnonneg : 0 ≤ xiCriticalScrewSeries h := by
    exact screwSeries_nonneg xiCriticalScrewWeight_nonneg h
  rw [abs_of_nonneg hnonneg]
  exact (screwSeries_le_screwHullMax xiCriticalScrewWeight_nonneg hsum h).trans_lt
    (screwHullMax_lt_fiftyEight_over_sixHundredTwentyFive_of_rh hRH)

theorem abs_unitRieszSuzukiGreen_lt_twoAndHalf_mul_of_suzuki_bound
    {C H : ℝ} (hC : 0 ≤ C)
    (hPsi : ∀ h : ℝ, 0 ≤ h → |suzukiPsi h| ≤ C)
    (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiGreen H| ≤ (5 / 2) * C +
      (1 / 4) * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| := by
  have hraw := unitRieszSuzukiGreen_eq_raw hH
  have hHH : |unitRieszSuzukiReporterDeriv H H * suzukiPsi H| ≤ (1 / 2) * C := by
    rw [unitRieszSuzukiReporterDeriv_H, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left
      (hPsi H (unitRieszSuzukiBase_pos.le.trans hH)) (by norm_num)
  have hI := abs_integral_suzukiPsi_mul_unitRieszSuzukiReporterSecond_le hC hPsi hH
  have hbasePsi :
      |suzukiPsi unitRieszSuzukiBase *
          unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase| ≤ C * (1 / 2) := by
    rw [abs_mul]
    exact mul_le_mul (hPsi unitRieszSuzukiBase unitRieszSuzukiBase_pos.le)
      (abs_unitRieszSuzukiReporterDeriv_le_half hH) (abs_nonneg _) hC
  have hbaseSlope :
      |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
          unitRieszSuzukiReporter H unitRieszSuzukiBase| ≤
        |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| * (1 / 4) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_unitRieszSuzukiReporter_le_quarter hH)
      (abs_nonneg _)
  rw [hraw]
  calc
    |unitRieszSuzukiReporterDeriv H H * suzukiPsi H -
          (∫ h in unitRieszSuzukiBase..H,
            suzukiPsi h * unitRieszSuzukiReporterSecond H h) -
        suzukiPsi unitRieszSuzukiBase *
          unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase +
        ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
          unitRieszSuzukiReporter H unitRieszSuzukiBase| ≤
        |unitRieszSuzukiReporterDeriv H H * suzukiPsi H| +
          |∫ h in unitRieszSuzukiBase..H,
            suzukiPsi h * unitRieszSuzukiReporterSecond H h| +
          |suzukiPsi unitRieszSuzukiBase *
            unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase| +
          |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
            unitRieszSuzukiReporter H unitRieszSuzukiBase| := by
      calc
        |_ + _| ≤
            |unitRieszSuzukiReporterDeriv H H * suzukiPsi H -
                (∫ h in unitRieszSuzukiBase..H,
                  suzukiPsi h * unitRieszSuzukiReporterSecond H h) -
              suzukiPsi unitRieszSuzukiBase *
                unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase| +
              |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
                unitRieszSuzukiReporter H unitRieszSuzukiBase| := abs_add_le _ _
        _ ≤ (|unitRieszSuzukiReporterDeriv H H * suzukiPsi H -
                (∫ h in unitRieszSuzukiBase..H,
                  suzukiPsi h * unitRieszSuzukiReporterSecond H h)| +
              |suzukiPsi unitRieszSuzukiBase *
                unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase|) +
              |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
                unitRieszSuzukiReporter H unitRieszSuzukiBase| := by
          gcongr
          exact abs_sub _ _
        _ ≤ ((|unitRieszSuzukiReporterDeriv H H * suzukiPsi H| +
                |∫ h in unitRieszSuzukiBase..H,
                  suzukiPsi h * unitRieszSuzukiReporterSecond H h|) +
              |suzukiPsi unitRieszSuzukiBase *
                unitRieszSuzukiReporterDeriv H unitRieszSuzukiBase|) +
              |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase *
                unitRieszSuzukiReporter H unitRieszSuzukiBase| := by
          gcongr
          exact abs_sub _ _
        _ = _ := by ring
    _ ≤ (5 / 2) * C +
        (1 / 4) * |ccmGuinandWeilXiScrewRightSlope unitRieszSuzukiBase| := by
      nlinarith [hHH, hI, hbasePsi, hbaseSlope]

theorem abs_unitRieszSuzukiGreen_lt_twoHundredFortyOne_over_fiveHundred_of_rh
    (hRH : RiemannHypothesis) {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiGreen H| < 241 / 500 := by
  have hPsi : ∀ h : ℝ, 0 ≤ h → |suzukiPsi h| ≤ (58 / 625 : ℝ) := by
    intro h _hh
    exact (abs_suzukiPsi_lt_fiftyEight_over_sixHundredTwentyFive_of_rh hRH h).le
  have hgreen := abs_unitRieszSuzukiGreen_lt_twoAndHalf_mul_of_suzuki_bound
    (C := (58 / 625 : ℝ)) (by norm_num) hPsi hH
  have hslope := abs_ccmGuinandWeilXiScrewRightSlope_unitRieszSuzukiBase_lt_one
  nlinarith

def unitRieszSuzukiPolarQuadraticCoeff : ℝ :=
  (2 / 3 : ℝ) * Real.exp (3 * unitRieszSuzukiBase / 2) +
    2 * Real.exp (unitRieszSuzukiBase / 2)

def unitRieszSuzukiPolarLinearThreshold : ℝ :=
  unitRieszSuzukiBase + 2 + Real.exp unitRieszSuzukiBase

theorem exp_three_quarters_lt_nine_fourths :
    Real.exp (3 / 4 : ℝ) < 9 / 4 := by
  have hb := Real.exp_bound (x := (3 / 4 : ℝ)) (by norm_num)
    (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb
  nlinarith [le_abs_self (Real.exp (3 / 4 : ℝ) - 269 / 128)]

theorem unitRieszSuzukiPolarQuadraticCoeff_lt_twentyOne_fifths :
    unitRieszSuzukiPolarQuadraticCoeff < 21 / 5 := by
  have hquarter := exp_unitRieszSuzukiBase_half_lt_thirteen_tenths
  norm_num [unitRieszSuzukiBase] at hquarter
  rw [unitRieszSuzukiPolarQuadraticCoeff]
  norm_num [unitRieszSuzukiBase]
  nlinarith [exp_three_quarters_lt_nine_fourths, hquarter]

theorem thirtyThree_eighths_lt_unitRieszSuzukiPolarLinearThreshold :
    (33 / 8 : ℝ) < unitRieszSuzukiPolarLinearThreshold := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  rw [unitRieszSuzukiPolarLinearThreshold]
  norm_num [unitRieszSuzukiBase]
  nlinarith

theorem unitRieszSuzukiPolarQuadraticCoeff_sub_two_ge_threeHundredSeventySeven_over_oneHundredNinetyTwo :
    377 / 192 ≤ unitRieszSuzukiPolarQuadraticCoeff - 2 := by
  have hthree := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) 4
  have hquarter := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at hthree hquarter
  rw [unitRieszSuzukiPolarQuadraticCoeff]
  norm_num [unitRieszSuzukiBase]
  nlinarith

theorem unitRieszSuzukiPolarLinearThreshold_sub_two_lt_fortyThree_twentieths :
    unitRieszSuzukiPolarLinearThreshold - 2 < 43 / 20 := by
  have hexp : Real.exp (1 / 2 : ℝ) < 33 / 20 := by
    by_contra h
    have hle : (33 / 20 : ℝ) ≤ Real.exp (1 / 2) := le_of_not_gt h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 33 / 20) hle 2
    have heq : Real.exp (1 / 2 : ℝ) ^ (2 : ℕ) = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
    rw [heq] at hp
    nlinarith [Real.exp_one_lt_d9]
  rw [unitRieszSuzukiPolarLinearThreshold]
  norm_num [unitRieszSuzukiBase]
  nlinarith

theorem exp_neg_two_lt_seven_fiftieths : Real.exp (-2) < (7 / 50 : ℝ) := by
  have hneg : Real.exp (-1) < (46 / 125 : ℝ) := by
    nlinarith [Real.exp_neg_one_lt_d9]
  have hsq : Real.exp (-2) = Real.exp (-1) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hsq]
  nlinarith [Real.exp_pos (-1)]

theorem sub_mul_exp_neg_half_le_two_exp_neg_half
    {c H : ℝ} (hc : c ≤ H) :
    (H - c) * Real.exp (-H / 2) ≤ 2 * Real.exp (-c / 2) := by
  have hx0 : 0 ≤ (H - c) / 2 := by linarith
  have hexp := Real.add_one_le_exp ((H - c) / 2)
  have hx : H - c ≤ 2 * Real.exp ((H - c) / 2) := by nlinarith
  calc
    (H - c) * Real.exp (-H / 2) ≤
        (2 * Real.exp ((H - c) / 2)) * Real.exp (-H / 2) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = 2 * Real.exp (-c / 2) := by
      rw [show 2 * Real.exp ((H - c) / 2) * Real.exp (-H / 2) =
        2 * (Real.exp ((H - c) / 2) * Real.exp (-H / 2)) by ring,
        ← Real.exp_add]
      congr 2
      ring

theorem abs_unitRieszSuzukiPolarCorrection_lt_seven_tenths
    {H : ℝ} (hH : Real.log 2 ≤ H) :
    |unitRieszSuzukiPolarCorrection H| < 7 / 10 := by
  let x : ℝ := Real.exp (-H / 2)
  let A : ℝ := unitRieszSuzukiPolarQuadraticCoeff
  let B : ℝ := unitRieszSuzukiPolarLinearThreshold
  have hx0 : 0 < x := Real.exp_pos _
  have hxpow : Real.exp (-H) = x ^ (2 : ℕ) := by
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hformula : unitRieszSuzukiPolarCorrection H = (H - B) * x + A * x ^ (2 : ℕ) := by
    rw [unitRieszSuzukiPolarCorrection_eq, hxpow]
    dsimp only [A, B, unitRieszSuzukiPolarQuadraticCoeff,
      unitRieszSuzukiPolarLinearThreshold, x]
    ring
  have hA0 : 0 < A := by
    dsimp only [A, unitRieszSuzukiPolarQuadraticCoeff]
    positivity
  have hAupper : A < 21 / 5 :=
    unitRieszSuzukiPolarQuadraticCoeff_lt_twentyOne_fifths
  have hAlower : 377 / 192 ≤ A - 2 :=
    unitRieszSuzukiPolarQuadraticCoeff_sub_two_ge_threeHundredSeventySeven_over_oneHundredNinetyTwo
  have hBupper : B - 2 < 43 / 20 :=
    unitRieszSuzukiPolarLinearThreshold_sub_two_lt_fortyThree_twentieths
  have hBlower : (33 / 8 : ℝ) < B :=
    thirtyThree_eighths_lt_unitRieszSuzukiPolarLinearThreshold
  have hHlinear : 2 * (1 - x) ≤ H := by
    have he := Real.add_one_le_exp (-H / 2)
    dsimp only [x]
    nlinarith
  have hlowerPoly : 0 < (377 / 192 : ℝ) * x ^ (2 : ℕ) - (43 / 20) * x + 7 / 10 := by
    nlinarith [sq_nonneg (2 * (377 / 192 : ℝ) * x - 43 / 20)]
  have hlower : -(7 / 10 : ℝ) < unitRieszSuzukiPolarCorrection H := by
    rw [hformula]
    have hHx : 2 * (1 - x) * x ≤ H * x :=
      mul_le_mul_of_nonneg_right hHlinear hx0.le
    have hAterm : (377 / 192 : ℝ) * x ^ (2 : ℕ) ≤ (A - 2) * x ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hAlower (sq_nonneg x)
    have hBterm : -(B - 2) * x > -(43 / 20 : ℝ) * x := by
      have := mul_lt_mul_of_pos_right hBupper hx0
      linarith
    nlinarith
  have hupper : unitRieszSuzukiPolarCorrection H < 7 / 10 := by
    rw [hformula]
    have hxlog : x < 71 / 100 := by
      have he : Real.exp (-H) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hhalf : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hhalf, hxpow] at he
      nlinarith
    by_cases hHtwo : H ≤ 2
    · have hbracket : H - B + A * x < 0 := by
        by_cases hHone : H ≤ 1
        · have hAx : A * x < (21 / 5 : ℝ) * (71 / 100) :=
            mul_lt_mul hAupper hxlog.le hx0 (by norm_num)
          nlinarith
        · have hHone' : 1 < H := lt_of_not_ge hHone
          have hxhalf : x < 8 / 13 := by
            have hehalf : (13 / 8 : ℝ) < Real.exp (1 / 2) := by
              have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 4
              norm_num [Finset.sum_range_succ, Nat.factorial] at hs
              nlinarith
            have hxle : x ≤ Real.exp (-(1 / 2 : ℝ)) := by
              dsimp only [x]
              exact Real.exp_le_exp.mpr (by linarith)
            have hprod : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
              rw [← Real.exp_add]
              norm_num
            have hinv : Real.exp (-(1 / 2 : ℝ)) < 8 / 13 := by
              nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]
            exact hxle.trans_lt hinv
          by_cases hHthree : H ≤ 3 / 2
          · have hAx : A * x < (21 / 5 : ℝ) * (8 / 13) :=
              mul_lt_mul hAupper hxhalf.le hx0 (by norm_num)
            nlinarith
          · have hHthree' : 3 / 2 < H := lt_of_not_ge hHthree
            have hxhalf' : x < 1 / 2 := by
              have hethree : (2 : ℝ) < Real.exp (3 / 4) := by
                have hs := Real.sum_le_exp_of_nonneg
                  (by norm_num : (0 : ℝ) ≤ 3 / 4) 4
                norm_num [Finset.sum_range_succ, Nat.factorial] at hs
                nlinarith
              have hxle : x ≤ Real.exp (-(3 / 4 : ℝ)) := by
                dsimp only [x]
                exact Real.exp_le_exp.mpr (by linarith)
              have hprod : Real.exp (-(3 / 4 : ℝ)) * Real.exp (3 / 4) = 1 := by
                rw [← Real.exp_add]
                norm_num
              have hinv : Real.exp (-(3 / 4 : ℝ)) < 1 / 2 := by
                nlinarith [Real.exp_pos (-(3 / 4 : ℝ))]
              exact hxle.trans_lt hinv
            have hAx : A * x < (21 / 5 : ℝ) * (1 / 2) :=
              mul_lt_mul hAupper hxhalf'.le hx0 (by norm_num)
            nlinarith
      have hvalue : (H - B) * x + A * x ^ (2 : ℕ) < 0 := by
        have hp : x * (H - B + A * x) < 0 :=
          mul_neg_of_pos_of_neg hx0 hbracket
        nlinarith
      exact hvalue.trans (by norm_num)
    · have htwoH : 2 < H := lt_of_not_ge hHtwo
      by_cases hHB : H ≤ B
      · have hfirst : (H - B) * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr hHB) hx0.le
        have hx2 : x ^ (2 : ℕ) < 7 / 50 := by
          rw [← hxpow]
          exact (Real.exp_lt_exp.mpr (by linarith : -H < -2)).trans
            exp_neg_two_lt_seven_fiftieths
        have hsecond : A * x ^ (2 : ℕ) < (21 / 5 : ℝ) * (7 / 50) :=
          mul_lt_mul hAupper hx2.le (sq_pos_of_pos hx0) (by norm_num)
        nlinarith
      · have hBH : B < H := lt_of_not_ge hHB
        have hBfour : 4 < B := hBlower.trans' (by norm_num)
        have hfirst0 := sub_mul_exp_neg_half_le_two_exp_neg_half hBH.le
        have hBexp : Real.exp (-B / 2) < 7 / 50 :=
          (Real.exp_lt_exp.mpr (by linarith : -B / 2 < -2)).trans
            exp_neg_two_lt_seven_fiftieths
        have hfirst : (H - B) * x < 7 / 25 := by
          dsimp only [x]
          nlinarith
        have hx2 : x ^ (2 : ℕ) < 1 / 50 := by
          rw [← hxpow]
          have he4 : Real.exp (-4) = Real.exp (-2) ^ (2 : ℕ) := by
            rw [← Real.exp_nat_mul]
            norm_num
          have he4lt : Real.exp (-4) < 1 / 50 := by
            rw [he4]
            nlinarith [Real.exp_pos (-2), exp_neg_two_lt_seven_fiftieths]
          exact (Real.exp_lt_exp.mpr (by linarith : -H < -4)).trans he4lt
        have hsecond : A * x ^ (2 : ℕ) < 21 / 250 := by
          have := mul_lt_mul hAupper hx2.le (sq_pos_of_pos hx0)
            (by norm_num : (0 : ℝ) ≤ 21 / 5)
          norm_num at this ⊢
          exact this
        nlinarith
  rw [abs_lt]
  exact ⟨hlower, hupper⟩

theorem unitRieszSuzukiArchDenominator_gt_seventyNine_oneHundredTwentyFifths :
    (79 / 125 : ℝ) < unitRieszSuzukiArchDenominator := by
  have he : Real.exp (-1) < (46 / 125 : ℝ) := by
    nlinarith [Real.exp_neg_one_lt_d9]
  rw [unitRieszSuzukiArchDenominator]
  norm_num [unitRieszSuzukiBase]
  nlinarith

theorem integral_unitRieszSuzukiArchQuarterMajorant
    (H : ℝ) :
    (∫ h in unitRieszSuzukiBase..H,
      (1 / 4 : ℝ) * Real.exp (-h / 2) / unitRieszSuzukiArchDenominator) =
      (1 / 2 : ℝ) *
        (Real.exp (-unitRieszSuzukiBase / 2) - Real.exp (-H / 2)) /
          unitRieszSuzukiArchDenominator := by
  have hderiv : ∀ h : ℝ, HasDerivAt
      (fun x : ℝ => -2 * Real.exp (-x / 2)) (Real.exp (-h / 2)) h := by
    intro h
    convert (hasDerivAt_exp_neg_half h).const_mul (-2 : ℝ) using 1
    all_goals first | rfl | ring_nf
  have hint :
      (∫ h in unitRieszSuzukiBase..H, Real.exp (-h / 2)) =
        2 * (Real.exp (-unitRieszSuzukiBase / 2) - Real.exp (-H / 2)) := by
    have hraw := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := unitRieszSuzukiBase) (b := H)
      (fun h _hh => hderiv h)
      ((by fun_prop : Continuous (fun h : ℝ => Real.exp (-h / 2))).intervalIntegrable _ _)
    linarith
  rw [show (fun h : ℝ =>
      (1 / 4 : ℝ) * Real.exp (-h / 2) / unitRieszSuzukiArchDenominator) =
      fun h => ((1 / 4 : ℝ) / unitRieszSuzukiArchDenominator) *
        Real.exp (-h / 2) by funext h; ring,
    intervalIntegral.integral_const_mul, hint]
  ring

theorem abs_unitRieszSuzukiArchCorrection_lt_seven_tenths
    {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    |unitRieszSuzukiArchCorrection H| < 7 / 10 := by
  let g : ℝ → ℝ := fun h =>
    (1 / 4 : ℝ) * Real.exp (-h / 2) / unitRieszSuzukiArchDenominator
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hpoint : ∀ h ∈ Set.Ioc unitRieszSuzukiBase H,
      ‖unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h‖ ≤ g h := by
    intro h hh
    have hhpos : 0 < h := unitRieszSuzukiBase_pos.trans_le hh.1.le
    have hdensity0 : 0 ≤ ccmPublishedArchimedeanDensity h := by
      rw [ccmPublishedArchimedeanDensity_eq_exp_neg_half_div hhpos]
      exact div_nonneg (Real.exp_pos _).le (by
        have he : Real.exp (-2 * h) < 1 := by
          rw [Real.exp_lt_one_iff]
          linarith
        linarith)
    have hdensity := ccmPublishedArchimedeanDensity_le_unitRieszSuzukiBase hh.1.le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdensity0]
    calc
      |unitRieszSuzukiReporter H h| * ccmPublishedArchimedeanDensity h ≤
          (1 / 4 : ℝ) *
            (Real.exp (-h / 2) / unitRieszSuzukiArchDenominator) :=
        mul_le_mul (abs_unitRieszSuzukiReporter_le_quarter hh.2)
          hdensity hdensity0 (by norm_num)
      _ = g h := by dsimp only [g]; ring
  have hnorm : ‖∫ h in unitRieszSuzukiBase..H,
      unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h‖ ≤
      ∫ h in unitRieszSuzukiBase..H, g h := by
    apply intervalIntegral.norm_integral_le_of_norm_le hH
    · filter_upwards [] with h hh
      exact hpoint h hh
    · exact hgcont.intervalIntegrable _ _
  have hintegral := integral_unitRieszSuzukiArchQuarterMajorant H
  have hmajorant : (∫ h in unitRieszSuzukiBase..H, g h) ≤
      (1 / 2 : ℝ) * Real.exp (-unitRieszSuzukiBase / 2) /
        unitRieszSuzukiArchDenominator := by
    dsimp only [g]
    rw [hintegral]
    apply div_le_div_of_nonneg_right _ unitRieszSuzukiArchDenominator_pos.le
    nlinarith [Real.exp_pos (-H / 2)]
  have hconstant :
      (1 / 2 : ℝ) * Real.exp (-unitRieszSuzukiBase / 2) /
          unitRieszSuzukiArchDenominator < 7 / 10 := by
    rw [div_lt_iff₀ unitRieszSuzukiArchDenominator_pos]
    have he := four_fifths_gt_exp_neg_unitRieszSuzukiBase_half
    have he' : Real.exp (-unitRieszSuzukiBase / 2) < (4 / 5 : ℝ) := by
      simpa only [neg_div] using he
    have hd := unitRieszSuzukiArchDenominator_gt_seventyNine_oneHundredTwentyFifths
    have hnum : (1 / 2 : ℝ) * Real.exp (-unitRieszSuzukiBase / 2) < 2 / 5 := by
      calc
        (1 / 2 : ℝ) * Real.exp (-unitRieszSuzukiBase / 2) <
            (1 / 2) * (4 / 5) := mul_lt_mul_of_pos_left he' (by norm_num)
        _ = 2 / 5 := by norm_num
    have hden : (2 / 5 : ℝ) < (7 / 10) * unitRieszSuzukiArchDenominator := by
      calc
        (2 / 5 : ℝ) < (7 / 10) * (79 / 125) := by norm_num
        _ < (7 / 10) * unitRieszSuzukiArchDenominator :=
          mul_lt_mul_of_pos_left hd (by norm_num)
    exact hnum.trans hden
  rw [unitRieszSuzukiArchCorrection, ← Real.norm_eq_abs]
  exact hnorm.trans_lt (hmajorant.trans_lt hconstant)

theorem abs_unitRieszCoherentCompletedOutgoingCharge_lt_two_of_riemannHypothesis
    (hRH : RiemannHypothesis) {N : ℕ} (hN : 2 ≤ N) :
    |unitRieszCoherentCompletedOutgoingCharge N| < 2 := by
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hN)
  have hlog : Real.log 2 ≤ Real.log N :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hNR (by exact_mod_cast hN)
  have hbase : unitRieszSuzukiBase ≤ Real.log N :=
    unitRieszSuzukiBase_lt_log_two.le.trans hlog
  have hgreen :=
    abs_unitRieszSuzukiGreen_lt_twoHundredFortyOne_over_fiveHundred_of_rh hRH hbase
  have hpolar := abs_unitRieszSuzukiPolarCorrection_lt_seven_tenths hlog
  have harch := abs_unitRieszSuzukiArchCorrection_lt_seven_tenths hbase
  have hout := unitRieszSuzuki_outgoing_eq_green hN
  rw [hout]
  calc
    |unitRieszSuzukiGreen (Real.log N) +
          unitRieszSuzukiPolarCorrection (Real.log N) -
        unitRieszSuzukiArchCorrection (Real.log N)| ≤
        |unitRieszSuzukiGreen (Real.log N)| +
          |unitRieszSuzukiPolarCorrection (Real.log N)| +
            |unitRieszSuzukiArchCorrection (Real.log N)| := by
      have hsub := abs_sub
        (unitRieszSuzukiGreen (Real.log N) +
          unitRieszSuzukiPolarCorrection (Real.log N))
        (unitRieszSuzukiArchCorrection (Real.log N))
      have hadd := abs_add_le (unitRieszSuzukiGreen (Real.log N))
        (unitRieszSuzukiPolarCorrection (Real.log N))
      linarith
    _ < 2 := by nlinarith

theorem unitRieszCoherentCompletedOutgoingProfile_le_pole_of_riemannHypothesis
    (hRH : RiemannHypothesis) {N : ℕ} (hN : 2 ≤ N) :
    ∀ u : ℝ, 0 < u →
      boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u ≤
        boundaryRelativeTrace polePacketProfile u := by
  apply (unitRieszCoherentCompletedOutgoingProfile_le_pole_iff hN).2
  have hcharge :=
    abs_unitRieszCoherentCompletedOutgoingCharge_lt_two_of_riemannHypothesis hRH hN
  have hrel := unitRieszCoherentCompletedOutgoingCharge_eq_resolvent_half hN
  have habsres :
      |criticalMellinChebyshevResolventSource (Real.log N)| < 4 := by
    have hres : criticalMellinChebyshevResolventSource (Real.log N) =
        2 * unitRieszCoherentCompletedOutgoingCharge N := by
      linarith
    rw [hres, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hp := pow_le_pow_left₀
    (abs_nonneg (criticalMellinChebyshevResolventSource (Real.log N))) habsres.le 2
  norm_num at hp
  exact hp

theorem riemannHypothesis_iff_unitRieszCoherentCompletedOutgoingProfile_le_pole :
    RiemannHypothesis ↔
      ∀ N : ℕ, 2 ≤ N → ∀ u : ℝ, 0 < u →
        boundaryRelativeTrace (unitRieszCoherentCompletedOutgoingProfile N) u ≤
          boundaryRelativeTrace polePacketProfile u := by
  constructor
  · intro hRH N hN
    exact unitRieszCoherentCompletedOutgoingProfile_le_pole_of_riemannHypothesis hRH hN
  · exact riemannHypothesis_of_unitRieszCoherentCompletedOutgoingProfile_le_pole

end RHTower
