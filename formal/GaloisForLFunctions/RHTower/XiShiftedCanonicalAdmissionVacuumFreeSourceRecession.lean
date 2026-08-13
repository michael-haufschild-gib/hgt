import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionNondegenerateSourceEffectivity
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalCurvatureRecession

/-!
# Vacuum-free adaptive arithmetic source recession

The nondegenerate null-flag source pays admission effectivity, but its odd unit channel leaves a
normalized vacuum floor.  Subtracting that unit inside the source polynomial preserves literal
arithmetic provenance and removes exactly the non-recessive channel.

This module proves the missing outgoing-ray law.  Exact reciprocal-mass coordinate transport gives
weight two to every diagonal Jacobi coefficient and weight four to every lower Jacobi coefficient.
Consequently the unit-renormalized source divided by current admitted norm tends to zero at every
fixed positive degree.  The same statement is proved for the literal adjacent-amplitude completed
`P^sharp` arithmetic aggregate, not a reporter applied after aggregation.
-/

open Filter Matrix MeasureTheory Polynomial Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open XiShiftedCanonicalAdmission

private theorem tendsto_actual_monicOrthoFirstCoeff_squareParam_zero (n : ℕ) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoFirstCoeff
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n)
      atTop (nhds 0) := by
  have hfactor : Tendsto (fun w : ℝ => (w ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : 2 ≠ 0))
  have hnormal := tendsto_dimensionless_monicOrthoFirstCoeff n
  have hrhs : Tendsto
      (fun w : ℝ => (w ^ 2)⁻¹ *
        HTGeometry.monicOrthoFirstCoeff (xiShiftedFarRightNormalizedMoment w) n)
      atTop (nhds 0) := by
    simpa using hfactor.mul hnormal
  apply hrhs.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 2),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 2)).PosDef := hA
  have hscale := normalizedFirstCoeff_eq_square_mul_actualFirstCoeff hw n hN' hA'
  rw [hscale]
  field_simp [ne_of_gt (lt_trans zero_lt_one hw)]

/-- Every fixed actual diagonal Jacobi coefficient vanishes on the square-mass ray. -/
theorem tendsto_actual_monicOrthoAlpha_squareParam_zero (n : ℕ) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoAlpha
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n)
      atTop (nhds 0) := by
  have hfactor : Tendsto (fun w : ℝ => (w ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : 2 ≠ 0))
  have hnormal := tendsto_dimensionless_monicOrthoAlpha n
  have hrhs : Tendsto
      (fun w : ℝ => (w ^ 2)⁻¹ *
        HTGeometry.monicOrthoAlpha (xiShiftedFarRightNormalizedMoment w) n)
      atTop (nhds 0) := by
    simpa using hfactor.mul hnormal
  apply hrhs.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 3),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 3),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 3)).PosDef := hA
  have hscale := normalizedAlpha_eq_square_mul_actualAlpha hw n hN' hA'
  rw [hscale]
  field_simp [ne_of_gt (lt_trans zero_lt_one hw)]

/-- Every positive-index actual lower Jacobi coefficient vanishes on the square-mass ray. -/
theorem tendsto_actual_monicOrthoBeta_squareParam_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n)
      atTop (nhds 0) := by
  have hfactor : Tendsto (fun w : ℝ => (w ^ 4)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by omega : 4 ≠ 0))
  have hnormal := tendsto_dimensionless_monicOrthoBeta hn
  have hrhs : Tendsto
      (fun w : ℝ => (w ^ 4)⁻¹ *
        HTGeometry.monicOrthoBeta (xiShiftedFarRightNormalizedMoment w) n)
      atTop (nhds 0) := by
    simpa using hfactor.mul hnormal
  apply hrhs.congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 3),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 3),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 3)).PosDef := hA
  have hscale := normalizedBeta_eq_fourth_mul_actualBeta hw n hN' hA'
  rw [hscale]
  field_simp [ne_of_gt (lt_trans zero_lt_one hw)]

/-- The entire vacuum-free Jacobi history recedes at every fixed positive degree. -/
theorem tendsto_nondegenerateNullFlagCompletedJacobiHistory_sub_one_squareParam_zero
    {n : ℕ} (_hn : 0 < n) :
    Tendsto
      (fun w : ℝ =>
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n - 1)
      atTop (nhds 0) := by
  let s : ℝ → ℕ → ℝ := fun w k => (xiShiftedReciprocalMoment (w ^ 2) k).re
  have halpha : ∀ j : ℕ,
      Tendsto (fun w : ℝ => HTGeometry.monicOrthoAlpha (s w) j ^ 2)
        atTop (nhds 0) := fun j => by
    simpa only [zero_pow (by omega : 2 ≠ 0)] using
      (tendsto_actual_monicOrthoAlpha_squareParam_zero j).pow 2
  have halphaSum : Tendsto
      (fun w : ℝ => ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoAlpha (s w) j ^ 2) atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.range n) (fun j _hj => halpha j)
  have hbeta : ∀ j : ℕ,
      Tendsto (fun w : ℝ => HTGeometry.monicOrthoBeta (s w) j)
        atTop (nhds 0) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [HTGeometry.monicOrthoBeta]
    · exact tendsto_actual_monicOrthoBeta_squareParam_zero (Nat.pos_of_ne_zero hj)
  have hbetaSum : Tendsto
      (fun w : ℝ => ∑ j ∈ Finset.range n,
        HTGeometry.monicOrthoBeta (s w) j) atTop (nhds 0) := by
    simpa using tendsto_finsetSum (Finset.range n) (fun j _hj => hbeta j)
  have hfirst := (tendsto_actual_monicOrthoFirstCoeff_squareParam_zero n).pow 2
  have halphaN := (tendsto_actual_monicOrthoAlpha_squareParam_zero n).pow 2
  have h := ((halphaSum.add (hbetaSum.const_mul 2)).add (hfirst.const_mul 2)).add halphaN
  convert h using 1
  · simp [HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory, s]
  · ring

/-- Shifted-arcsine boundary value of vacuum-free nondegenerate source density. -/
def xiShiftedVacuumFreeArcsineJacobiHistory (n : ℕ) : ℝ :=
  HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
    GaloisForLFunctions.HTGeometry.normalizedCentralBinom n - 1

theorem xiShiftedVacuumFreeArcsineJacobiHistory_one :
    xiShiftedVacuumFreeArcsineJacobiHistory 1 = 1 := by
  rw [xiShiftedVacuumFreeArcsineJacobiHistory,
    HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory,
    HTGeometry.monicOrthoFirstCoeff_eq_neg_sum
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm]
  simp_rw [monicOrthoAlpha_normalizedCentralBinom]
  simp [HTGeometry.monicOrthoBeta]
  norm_num

theorem xiShiftedVacuumFreeArcsineJacobiHistory_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    xiShiftedVacuumFreeArcsineJacobiHistory n =
      (4 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 2) / 8 := by
  rw [xiShiftedVacuumFreeArcsineJacobiHistory,
    HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory,
    XiShiftedCanonicalAdmission.sum_monicOrthoBeta_normalizedCentralBinom_of_two_le hn,
    HTGeometry.monicOrthoFirstCoeff_eq_neg_sum
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom_positiveMomentForm]
  simp_rw [monicOrthoAlpha_normalizedCentralBinom]
  simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem xiShiftedVacuumFreeArcsineJacobiHistory_pos
    {n : ℕ} (hn : 0 < n) :
    0 < xiShiftedVacuumFreeArcsineJacobiHistory n := by
  rcases n with _ | _ | n
  · omega
  · rw [xiShiftedVacuumFreeArcsineJacobiHistory_one]
    norm_num
  · rw [xiShiftedVacuumFreeArcsineJacobiHistory_of_two_le (by omega)]
    positivity

/-- Dimensionless vacuum-free source density converges to its exact positive arcsine value. -/
theorem tendsto_dimensionless_nondegenerateNullFlagCompletedJacobiHistory_sub_one
    (n : ℕ) :
    Tendsto
      (fun w : ℝ =>
        HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (xiShiftedFarRightNormalizedMoment w) n - 1)
      atTop (nhds (xiShiftedVacuumFreeArcsineJacobiHistory n)) := by
  let arc : ℕ → ℝ := GaloisForLFunctions.HTGeometry.normalizedCentralBinom
  have halpha : ∀ j : ℕ,
      Tendsto
        (fun w : ℝ => HTGeometry.monicOrthoAlpha
          (xiShiftedFarRightNormalizedMoment w) j ^ 2)
        atTop (nhds (HTGeometry.monicOrthoAlpha arc j ^ 2)) := fun j => by
    simpa [arc, monicOrthoAlpha_normalizedCentralBinom] using
      (tendsto_dimensionless_monicOrthoAlpha j).pow 2
  have halphaSum := tendsto_finsetSum (Finset.range n) (fun j _hj => halpha j)
  have hbeta : ∀ j : ℕ,
      Tendsto
        (fun w : ℝ => HTGeometry.monicOrthoBeta
          (xiShiftedFarRightNormalizedMoment w) j)
        atTop (nhds (HTGeometry.monicOrthoBeta arc j)) := by
    intro j
    by_cases hj : j = 0
    · subst j
      simp [HTGeometry.monicOrthoBeta]
    · exact tendsto_dimensionless_monicOrthoBeta (Nat.pos_of_ne_zero hj)
  have hbetaSum := tendsto_finsetSum (Finset.range n) (fun j _hj => hbeta j)
  have hfirst := (tendsto_dimensionless_monicOrthoFirstCoeff n).pow 2
  have halphaN := halpha n
  have h := ((halphaSum.add (hbetaSum.const_mul 2)).add (hfirst.const_mul 2)).add halphaN
  convert h using 1
  · simp [HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory]
  · simp [xiShiftedVacuumFreeArcsineJacobiHistory, arc,
      HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory]

/-- Exact coordinate law: vacuum-free source density has reciprocal-mass weight four. -/
theorem normalized_nondegenerateNullFlagCompletedJacobiHistory_sub_one_eq_fourth_mul_actual
    {w : ℝ} (hw : 1 < w) (n : ℕ)
    (hN : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef)
    (hA : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 3)).PosDef) :
    HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
        (xiShiftedFarRightNormalizedMoment w) n - 1 =
      w ^ 4 *
        (HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n - 1) := by
  let sn : ℕ → ℝ := xiShiftedFarRightNormalizedMoment w
  let sa : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re
  have halphaSum :
      (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha sn j ^ 2) =
        w ^ 4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha sa j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have hNj : (HTGeometry.momentHankelMatrix sn (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix sa (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA
    have hscale := normalizedAlpha_eq_square_mul_actualAlpha hw j hNj hAj
    rw [hscale]
    ring
  have hbetaSum :
      (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta sn j) =
        w ^ 4 * (∑ j ∈ Finset.range n, HTGeometry.monicOrthoBeta sa j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    have hNj : (HTGeometry.momentHankelMatrix sn (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hN
    have hAj : (HTGeometry.momentHankelMatrix sa (j + 3)).PosDef :=
      momentHankel_posDef_of_le (by omega) hA
    have hscale := normalizedBeta_eq_fourth_mul_actualBeta hw j hNj hAj
    exact hscale
  have hNsmall : (HTGeometry.momentHankelMatrix sn (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hN
  have hAsmall : (HTGeometry.momentHankelMatrix sa (n + 2)).PosDef :=
    momentHankel_posDef_of_le (by omega) hA
  have hfirst := normalizedFirstCoeff_eq_square_mul_actualFirstCoeff
    hw n hNsmall hAsmall
  have halpha := normalizedAlpha_eq_square_mul_actualAlpha hw n hN hA
  rw [HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory,
    HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory,
    halphaSum, hbetaSum, hfirst, halpha]
  ring

/-- **Sharp fixed-degree recession rate.**  In actual mass `y = w²`, vacuum-free source density
is exactly order `y⁻²`, with a strictly positive shifted-arcsine leading coefficient. -/
theorem tendsto_fourth_mul_nondegenerateNullFlagCompletedJacobiHistory_sub_one_squareParam
    (n : ℕ) :
    Tendsto
      (fun w : ℝ => w ^ 4 *
        (HTGeometry.nondegenerateNullFlagCompletedDegreeCenteredOrthoJacobiHistory
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) n - 1))
      atTop (nhds (xiShiftedVacuumFreeArcsineJacobiHistory n)) := by
  apply (tendsto_dimensionless_nondegenerateNullFlagCompletedJacobiHistory_sub_one n).congr'
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually (n + 3),
    xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 3),
    eventually_gt_atTop (1 : ℝ)] with w hN hA hw
  have hN' : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 3)).PosDef := by
    simpa [xiShiftedFarRightNormalizedHankelMatrix] using hN
  have hA' : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re) (n + 3)).PosDef := hA
  exact (normalized_nondegenerateNullFlagCompletedJacobiHistory_sub_one_eq_fourth_mul_actual
    hw n hN' hA')

/-- **Vacuum-free source recession.**  Source-first unit renormalization removes exactly the
non-recessive channel: source divided by twice current admitted norm tends to zero. -/
theorem tendsto_unitRenormalizedNondegenerateNullFlagSourceMass_div_norm_squareParam_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ =>
        xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass (w ^ 2) n /
          (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n))
      atTop (nhds 0) := by
  apply (tendsto_nondegenerateNullFlagCompletedJacobiHistory_sub_one_squareParam_zero hn).congr'
  filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2)]
      with w hH
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm (w ^ 2) n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_norm_mul_history_sub_one
    hn hH]
  field_simp [hnorm.ne']

/-- Exact leading law for normalized vacuum-free arithmetic source on square mass. -/
theorem tendsto_fourth_mul_unitRenormalizedSourceMass_div_norm_squareParam
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => w ^ 4 *
        (xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass (w ^ 2) n /
          (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n)))
      atTop (nhds (xiShiftedVacuumFreeArcsineJacobiHistory n)) := by
  apply (tendsto_fourth_mul_nondegenerateNullFlagCompletedJacobiHistory_sub_one_squareParam
    n).congr'
  filter_upwards [xiShiftedMomentHankelMatrix_squareParam_posDef_eventually (n + 2)]
      with w hH
  have hnorm : 0 < xiShiftedCanonicalAdmissionNorm (w ^ 2) n := by
    rw [xiShiftedCanonicalAdmissionNorm_eq_monicOrthoNorm hH]
    exact HTGeometry.monicOrthoNorm_pos_below
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH) (by omega)
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_eq_norm_mul_history_sub_one
    hn hH]
  field_simp [hnorm.ne']

/-- Actual-mass form: normalized vacuum-free arithmetic source has sharp `y⁻²` recession. -/
theorem tendsto_square_mul_unitRenormalizedSourceMass_div_norm
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun y : ℝ => y ^ 2 *
        (xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
          (2 * xiShiftedCanonicalAdmissionNorm y n)))
      atTop (nhds (xiShiftedVacuumFreeArcsineJacobiHistory n)) := by
  have h := (tendsto_fourth_mul_unitRenormalizedSourceMass_div_norm_squareParam hn).comp
    Real.tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply]
  have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have hfourth : (Real.sqrt y) ^ 4 = y ^ 2 := by
    calc
      (Real.sqrt y) ^ 4 = ((Real.sqrt y) ^ 2) ^ 2 := by ring
      _ = y ^ 2 := by rw [hsq]
  rw [hfourth, hsq]

/-- **Literal arithmetic recession law.**  Current and next canonical amplitudes enter the
completed rational--Gamma/von-Mangoldt aggregate before the vacuum is removed.  Its normalized
source density tends to zero at every fixed degree. -/
theorem tendsto_literal_unitRenormalizedAdaptiveMixedSource_div_norm_zero
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ =>
        xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w n
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) (n + 1)) /
          (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n))
      atTop (nhds 0) := by
  apply (tendsto_unitRenormalizedNondegenerateNullFlagSourceMass_div_norm_squareParam_zero
    hn).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_sq_eq_arithmetic
    (by linarith : 1 / 2 < w) n]

/-- Sharp literal source-first asymptotic: after forced weight-four completion, the adaptive
mixed rational--Gamma/von-Mangoldt source quotient converges to positive arcsine history. -/
theorem tendsto_fourth_mul_literal_unitRenormalizedAdaptiveMixedSource_div_norm
    {n : ℕ} (hn : 0 < n) :
    Tendsto
      (fun w : ℝ => w ^ 4 *
        (xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource w n
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) (n + 1)) /
          (2 * xiShiftedCanonicalAdmissionNorm (w ^ 2) n)))
      atTop (nhds (xiShiftedVacuumFreeArcsineJacobiHistory n)) := by
  apply (tendsto_fourth_mul_unitRenormalizedSourceMass_div_norm_squareParam hn).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with w hw
  rw [xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass_sq_eq_arithmetic
    (by linarith : 1 / 2 < w) n]

/-! ## Actual integral source action -/

/-- **Vacuum-free arithmetic integral Lipschitz law.**  Across an actual positive chamber,
normalized unit-renormalized source mass pays squared logarithmic motion of current admission.
Both adaptive amplitudes occur inside the source polynomial before arithmetic aggregation. -/
theorem log_norm_sub_log_norm_sq_le_unitRenormalizedSource_action
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) {n : ℕ} (hn : 0 < n)
    (hH : ∀ y ∈ Icc a b,
      (HTGeometry.momentHankelMatrix
        (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    (hR : IntervalIntegrable
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n) volume a b)
    (hR2 : IntervalIntegrable
      (fun y => xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2) volume a b)
    (hsource : IntervalIntegrable
      (fun y =>
        xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
          (2 * xiShiftedCanonicalAdmissionNorm y n)) volume a b) :
    (Real.log (xiShiftedCanonicalAdmissionNorm b n) -
        Real.log (xiShiftedCanonicalAdmissionNorm a n)) ^ 2 ≤
      (b - a) * xiShiftedNondegenerateSourceEffectivityWeight n *
        ∫ y in a..b,
          xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
            (2 * xiShiftedCanonicalAdmissionNorm y n) := by
  have hftc := integral_xiShiftedCanonicalAdmissionEffectivityRate_eq_log_norm_ratio
    hab ha hn hH hR
  let f : ℝ → ℝ := fun y => xiShiftedCanonicalAdmissionEffectivityRate y n
  let mu : Measure ℝ := volume.restrict (Ioc a b)
  have hfmu : Integrable f mu := hR.1
  have hsqmu : Integrable (fun y => f y ^ 2) mu := hR2.1
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) mu := by
    change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc a b) volume
    exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have honeSq : Integrable (fun _ : ℝ => (1 : ℝ) ^ 2) mu := by
    simpa only [one_pow] using hone
  have hcsRaw := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := mu)
    hone.aestronglyMeasurable hfmu.aestronglyMeasurable honeSq hsqmu
  have hmu : mu.real univ = b - a := by
    simp [mu, Measure.real, Real.volume_Ioc, hab]
  have hfIntegral : ∫ y, f y ∂mu = ∫ y in a..b, f y := by
    rw [intervalIntegral.integral_of_le hab]
  have hfsqIntegral : ∫ y, f y ^ 2 ∂mu = ∫ y in a..b, f y ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
  simp only [one_mul, one_pow] at hcsRaw
  rw [MeasureTheory.integral_const] at hcsRaw
  simp only [smul_eq_mul, mul_one] at hcsRaw
  have hcs : (∫ y in a..b, f y) ^ 2 ≤
      (b - a) * ∫ y in a..b, f y ^ 2 := by
    simpa only [hmu, hfIntegral, hfsqIntegral] using hcsRaw
  have hpoint : ∀ y ∈ Icc a b,
      xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2 ≤
        xiShiftedNondegenerateSourceEffectivityWeight n *
          (xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
            (2 * xiShiftedCanonicalAdmissionNorm y n)) := by
    intro y hy
    exact effectivity_sq_le_weight_mul_unitRenormalizedSourceMass_div_norm
      hn (hH y hy)
  have hmono :
      (∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2) ≤
        ∫ y in a..b, xiShiftedNondegenerateSourceEffectivityWeight n *
          (xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
            (2 * xiShiftedCanonicalAdmissionNorm y n)) :=
    intervalIntegral.integral_mono_on hab hR2
      (hsource.const_mul (xiShiftedNondegenerateSourceEffectivityWeight n)) hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  change (∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n) ^ 2 ≤
      (b - a) * ∫ y in a..b,
        xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2 at hcs
  calc
    (Real.log (xiShiftedCanonicalAdmissionNorm b n) -
        Real.log (xiShiftedCanonicalAdmissionNorm a n)) ^ 2 =
        (∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n) ^ 2 := by
          rw [hftc]
          ring
    _ ≤ (b - a) *
        ∫ y in a..b, xiShiftedCanonicalAdmissionEffectivityRate y n ^ 2 := hcs
    _ ≤ (b - a) *
        (xiShiftedNondegenerateSourceEffectivityWeight n *
          ∫ y in a..b,
            xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
              (2 * xiShiftedCanonicalAdmissionNorm y n)) :=
      mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hab)
    _ = (b - a) * xiShiftedNondegenerateSourceEffectivityWeight n *
        ∫ y in a..b,
          xiShiftedCanonicalUnitRenormalizedNondegenerateNullFlagSourceMass y n /
            (2 * xiShiftedCanonicalAdmissionNorm y n) := by ring

end

end RHTower
