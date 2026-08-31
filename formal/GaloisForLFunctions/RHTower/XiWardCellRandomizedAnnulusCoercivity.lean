import GaloisForLFunctions.RHTower.XiWardSourceWindowMultiplicity
import GaloisForLFunctions.RHTower.IntervalAutocorrelation
import GaloisForLFunctions.HTGeometry.LBitSupportLocalReporterLaw

/-!
# Cell-randomized Ward annulus coercivity

The ordinary two-line Ward annulus has zero spatial mean, so distant ordinate
cross terms can cancel its positive diagonal.  This file isolates a way around
that obstruction.  Split positive ordinates into unit cells and attach one
Rademacher sign to each cell.  Averaging signs deletes inter-cell terms.  The
remaining within-cell terms are uniformly positive, including the reflected
`gamma_i + gamma_j` channel.  Unit cells already give a positive reserve;
half-unit cells sharpen it past `3/8`, hence past the exact `3π` Ward charge
needed by the three-quarters gate.

Everything below is finite and divisor-agnostic algebra.  The remaining
producer problem is to realize the cell signs before scalarization by a
source-side pole--Gamma--von-Mangoldt transform.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

noncomputable local instance wardCellFintypeForallBool
    {κ : Type*} [Fintype κ] :
    Fintype (κ → Bool) :=
  Fintype.ofFinite _

/-- Difference of two Cauchy cross kernels when their common total width is
advanced by `D`. -/
def wardAnnulusCrossKernel (A D delta : ℝ) : ℝ :=
  A / (A ^ 2 + delta ^ 2) -
    (A + D) / ((A + D) ^ 2 + delta ^ 2)

/-- Exact numerator of the Ward annulus cross kernel.  Its sign changes only
at `delta² = A(A+D)`. -/
theorem wardAnnulusCrossKernel_eq
    {A D delta : ℝ} (hA : 0 < A) (hD : 0 < D) :
    wardAnnulusCrossKernel A D delta =
      D * (A * (A + D) - delta ^ 2) /
        ((A ^ 2 + delta ^ 2) * ((A + D) ^ 2 + delta ^ 2)) := by
  have hAD : 0 < A + D := by positivity
  have h₁ : 0 < A ^ 2 + delta ^ 2 := by positivity
  have h₂ : 0 < (A + D) ^ 2 + delta ^ 2 := by positivity
  unfold wardAnnulusCrossKernel
  field_simp [h₁.ne', h₂.ne']
  ring

/-- Near-channel reserve at the source-safe ten-unit annulus. -/
theorem one_fourth_le_wardAnnulusCrossKernel_twenty
    {A delta : ℝ} (hAlo : 1 ≤ A) (hAhi : A ≤ 3)
    (hdelta : delta ^ 2 ≤ 1) :
    1 / 4 ≤ wardAnnulusCrossKernel A 20 delta := by
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hAlo
  have hA20 : 0 < A + 20 := by positivity
  have hden : 0 < A ^ 2 + delta ^ 2 := by positivity
  have hdenMax : A ^ 2 + delta ^ 2 ≤ A ^ 2 + 1 := by linarith
  have hfirst : A / (A ^ 2 + 1) ≤ A / (A ^ 2 + delta ^ 2) :=
    div_le_div_of_nonneg_left hA.le hden hdenMax
  have hsecond :
      (A + 20) / ((A + 20) ^ 2 + delta ^ 2) ≤ 1 / (A + 20) := by
    have hsq : 0 < (A + 20) ^ 2 := sq_pos_of_pos hA20
    have hfull : 0 < (A + 20) ^ 2 + delta ^ 2 := by positivity
    rw [div_le_div_iff₀ hfull hA20]
    nlinarith [sq_nonneg delta]
  have hpoly : 0 ≤ (3 - A) * (A ^ 2 + 23 * A - 10) := by
    apply mul_nonneg
    · linarith
    · nlinarith
  have hbase : 1 / 4 ≤ A / (A ^ 2 + 1) - 1 / (A + 20) := by
    have hAden : 0 < A ^ 2 + 1 := by positivity
    rw [le_sub_iff_add_le]
    field_simp [hAden.ne', hA20.ne']
    nlinarith
  unfold wardAnnulusCrossKernel
  linarith

/-- No reflected far channel can lose more than `1/21` at the same annulus. -/
theorem neg_one_twentyOne_le_wardAnnulusCrossKernel_twenty
    {A delta : ℝ} (hA : 1 ≤ A) :
    -(1 / 21 : ℝ) ≤ wardAnnulusCrossKernel A 20 delta := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA20 : 0 < A + 20 := by positivity
  have hfull : 0 < (A + 20) ^ 2 + delta ^ 2 := by positivity
  have htermNonneg : 0 ≤ A / (A ^ 2 + delta ^ 2) := by positivity
  have hfar :
      (A + 20) / ((A + 20) ^ 2 + delta ^ 2) ≤ 1 / (A + 20) := by
    rw [div_le_div_iff₀ hfull hA20]
    nlinarith [sq_nonneg delta]
  have hinv : 1 / (A + 20) ≤ 1 / 21 := by
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  unfold wardAnnulusCrossKernel
  linarith

/-- Sharp enough uniform control of the arbitrary reflected channel.  The
crude `-1/21` bound discards the positive narrow-line term; retaining it
improves the loss to `-3/100` without any ordinate restriction. -/
theorem neg_three_hundredths_le_wardAnnulusCrossKernel_twenty
    {A delta : ℝ} (hAlo : 1 ≤ A) :
    -(3 / 100 : ℝ) ≤ wardAnnulusCrossKernel A 20 delta := by
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hAlo
  have hA20 : 0 < A + 20 := by positivity
  have hden₁ : 0 < A ^ 2 + delta ^ 2 := by positivity
  have hden₂ : 0 < (A + 20) ^ 2 + delta ^ 2 := by positivity
  have hs : 21 ≤ A * (A + 20) := by nlinarith
  have hsq := sq_nonneg (3 * (delta ^ 2 + A * (A + 20)) - 400)
  have hpositive :
      0 ≤ 3 * ((A ^ 2 + delta ^ 2) *
          ((A + 20) ^ 2 + delta ^ 2)) +
        2000 * (A * (A + 20) - delta ^ 2) := by
    nlinarith
  rw [wardAnnulusCrossKernel_eq hA (by norm_num)]
  rw [le_div_iff₀ (mul_pos hden₁ hden₂)]
  nlinarith

/-- Near-channel reserve for half-unit cells.  The exact safe width range is
`A ≤ 101/50`; keeping that endpoint instead of rounding it to `3` raises the
near reserve to `21/50`. -/
theorem twentyOne_fiftieth_le_wardAnnulusCrossKernel_twenty
    {A delta : ℝ} (hAlo : 1 ≤ A) (hAhi : A ≤ 101 / 50)
    (hdelta : delta ^ 2 ≤ 1 / 4) :
    21 / 50 ≤ wardAnnulusCrossKernel A 20 delta := by
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) hAlo
  have hA20 : 0 < A + 20 := by positivity
  have hden : 0 < A ^ 2 + delta ^ 2 := by positivity
  have hdenMax : A ^ 2 + delta ^ 2 ≤ A ^ 2 + 1 / 4 := by linarith
  have hfirst : A / (A ^ 2 + 1 / 4) ≤ A / (A ^ 2 + delta ^ 2) :=
    div_le_div_of_nonneg_left hA.le hden hdenMax
  have hsecond :
      (A + 20) / ((A + 20) ^ 2 + delta ^ 2) ≤ 1 / (A + 20) := by
    have hfull : 0 < (A + 20) ^ 2 + delta ^ 2 := by positivity
    rw [div_le_div_iff₀ hfull hA20]
    nlinarith [sq_nonneg delta]
  have hbase : 21 / 50 ≤ A / (A ^ 2 + 1 / 4) - 1 / (A + 20) := by
    by_cases hsmall : A ≤ 6 / 5
    · have hA2 : A ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by nlinarith
      have hdenUpper : A ^ 2 + 1 / 4 ≤ 169 / 100 := by nlinarith
      have hdenPos : 0 < A ^ 2 + 1 / 4 := by positivity
      have hfirstCoarse : 100 / 169 ≤ A / (A ^ 2 + 1 / 4) := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 169) hdenPos]
        nlinarith
      have hsecondCoarse : 1 / (A + 20) ≤ 1 / 21 := by
        exact one_div_le_one_div_of_le (by norm_num) (by linarith)
      norm_num at hfirstCoarse hsecondCoarse ⊢
      linarith
    · have hAlarge : 6 / 5 < A := lt_of_not_ge hsmall
      let P : ℝ → ℝ := fun x =>
        -168 * x ^ 3 - 3360 * x ^ 2 + 7958 * x - 940
      have hfactor :
          P A = P (101 / 50) + (101 / 50 - A) *
            (168 * (A ^ 2 + A * (101 / 50) + (101 / 50) ^ 2) +
              3360 * (A + 101 / 50) - 7958) := by
        dsimp [P]
        ring
      have hbracket :
          0 ≤ 168 * (A ^ 2 + A * (101 / 50) + (101 / 50) ^ 2) +
            3360 * (A + 101 / 50) - 7958 := by
        have hAnonneg : 0 ≤ A := hA.le
        nlinarith [sq_nonneg A]
      have hendpoint : 0 < P (101 / 50) := by
        norm_num [P]
      have hP : 0 ≤ P A := by
        rw [hfactor]
        positivity
      have hdenPos : 0 < A ^ 2 + 1 / 4 := by positivity
      rw [le_sub_iff_add_le]
      rw [div_add_div] <;> try positivity
      rw [div_le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 50) hA20) hdenPos]
      dsimp [P] at hP
      nlinarith
  unfold wardAnnulusCrossKernel
  linarith

/-- One Schwarz-pair cross entry: near same-sign interaction plus the far
reflected interaction. -/
def wardReflectedPairAnnulusCross
    (x y beta gamma : ℝ) : ℝ :=
  wardAnnulusCrossKernel (x + y) 20 (beta - gamma) +
    wardAnnulusCrossKernel (x + y) 20 (beta + gamma)

/-- Uniform within-unit-cell positivity.  Widths are exactly the range
created by the source-safe line `51/100` and a transverse displacement in
`(0,1/2)`. -/
theorem seventeen_eightyFour_le_wardReflectedPairAnnulusCross
    {x y beta gamma : ℝ}
    (hxlo : 51 / 100 ≤ x) (hxhi : x ≤ 101 / 100)
    (hylo : 51 / 100 ≤ y) (hyhi : y ≤ 101 / 100)
    (hcell : (beta - gamma) ^ 2 ≤ 1) :
    17 / 84 ≤ wardReflectedPairAnnulusCross x y beta gamma := by
  have hAlo : 1 ≤ x + y := by linarith
  have hAhi : x + y ≤ 3 := by linarith
  have hnear := one_fourth_le_wardAnnulusCrossKernel_twenty
    hAlo hAhi hcell
  have hfar := neg_one_twentyOne_le_wardAnnulusCrossKernel_twenty
    (delta := beta + gamma) hAlo
  unfold wardReflectedPairAnnulusCross
  norm_num at hnear hfar ⊢
  linarith

/-- Half-unit cells cross the exact `3/8` kernel threshold.  The near
interaction pays `21/50`; the reflected channel loses at most `3/100`. -/
theorem three_eighths_le_wardReflectedPairAnnulusCross
    {x y beta gamma : ℝ}
    (hxlo : 51 / 100 ≤ x) (hxhi : x ≤ 101 / 100)
    (hylo : 51 / 100 ≤ y) (hyhi : y ≤ 101 / 100)
    (hcell : (beta - gamma) ^ 2 ≤ 1 / 4) :
    3 / 8 ≤ wardReflectedPairAnnulusCross x y beta gamma := by
  have hAlo : 1 ≤ x + y := by linarith
  have hAhi : x + y ≤ 101 / 50 := by linarith
  have hnear := twentyOne_fiftieth_le_wardAnnulusCrossKernel_twenty
    hAlo hAhi hcell
  have hfar := neg_three_hundredths_le_wardAnnulusCrossKernel_twenty
    (delta := beta + gamma) hAlo
  unfold wardReflectedPairAnnulusCross
  norm_num at hnear hfar ⊢
  linarith

/-- A complete finite packet inside one unit ordinate cell is coercive.  This
is the block surviving independent sign averaging across cells. -/
theorem finite_cell_wardReflectedPairAnnulusCross_lower
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x beta weight : ι → ℝ)
    (hxlo : ∀ i ∈ S, 51 / 100 ≤ x i)
    (hxhi : ∀ i ∈ S, x i ≤ 101 / 100)
    (hcell : ∀ i ∈ S, ∀ j ∈ S, (beta i - beta j) ^ 2 ≤ 1)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) :
    (17 / 84 : ℝ) * (∑ i ∈ S, weight i) ^ 2 ≤
      ∑ i ∈ S, ∑ j ∈ S,
        weight i * weight j *
          wardReflectedPairAnnulusCross (x i) (x j) (beta i) (beta j) := by
  have hsum :
      ∑ i ∈ S, ∑ j ∈ S, (17 / 84 : ℝ) * (weight j * weight i) ≤
        ∑ i ∈ S, ∑ j ∈ S,
          weight i * weight j *
            wardReflectedPairAnnulusCross (x i) (x j) (beta i) (beta j) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hcross := seventeen_eightyFour_le_wardReflectedPairAnnulusCross
      (hxlo i hi) (hxhi i hi) (hxlo j hj) (hxhi j hj) (hcell i hi j hj)
    have hw : 0 ≤ weight i * weight j :=
      mul_nonneg (hweight i hi) (hweight j hj)
    nlinarith
  calc
    (17 / 84 : ℝ) * (∑ i ∈ S, weight i) ^ 2 =
        ∑ i ∈ S, ∑ j ∈ S, (17 / 84 : ℝ) * (weight j * weight i) := by
      simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := hsum

/-! ## Identification with the actual Ward response -/

/-- One shifted Lorentzian half in the real Ward channel. -/
def wardLorentzianHalf (x beta t : ℝ) : ℝ :=
  x / (x ^ 2 + (t + beta) ^ 2)

/-- The two reflected Lorentzian halves carried by one Schwarz pair. -/
def wardReflectedLorentzianProfile (x beta t : ℝ) : ℝ :=
  2 * wardLorentzianHalf x beta t +
    2 * wardLorentzianHalf x (-beta) t

theorem integrable_wardLorentzianHalf_mul
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (beta gamma : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ =>
      wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t) := by
  simpa only [wardLorentzianHalf] using
    integrable_mul_lorentzianHalves_general hx hy beta gamma

theorem integral_wardLorentzianHalf_mul
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (beta gamma : ℝ) :
    (∫ t : ℝ,
      wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t) =
      Real.pi * (x + y) /
        ((x + y) ^ 2 + (beta - gamma) ^ 2) := by
  simpa only [wardLorentzianHalf] using
    integral_mul_lorentzianHalves_general hx hy beta gamma

/-- Exact cross mass of two complete reflected Schwarz-pair profiles. -/
theorem integral_wardReflectedLorentzianProfile_mul
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (beta gamma : ℝ) :
    (∫ t : ℝ,
      wardReflectedLorentzianProfile x beta t *
        wardReflectedLorentzianProfile y gamma t) =
      8 * Real.pi *
        ((x + y) / ((x + y) ^ 2 + (beta - gamma) ^ 2) +
          (x + y) / ((x + y) ^ 2 + (beta + gamma) ^ 2)) := by
  have hpp := integrable_wardLorentzianHalf_mul hx hy beta gamma
  have hpm := integrable_wardLorentzianHalf_mul hx hy beta (-gamma)
  have hmp := integrable_wardLorentzianHalf_mul hx hy (-beta) gamma
  have hmm := integrable_wardLorentzianHalf_mul hx hy (-beta) (-gamma)
  rw [show (fun t : ℝ =>
      wardReflectedLorentzianProfile x beta t *
        wardReflectedLorentzianProfile y gamma t) =
      fun t : ℝ => 4 *
        (wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t +
          wardLorentzianHalf x beta t * wardLorentzianHalf y (-gamma) t +
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y gamma t +
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y (-gamma) t) by
    funext t
    unfold wardReflectedLorentzianProfile
    ring]
  rw [MeasureTheory.integral_const_mul]
  have hsplit :
      (∫ t : ℝ,
        wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t +
          wardLorentzianHalf x beta t * wardLorentzianHalf y (-gamma) t +
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y gamma t +
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y (-gamma) t) =
        (∫ t : ℝ,
          wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t) +
        (∫ t : ℝ,
          wardLorentzianHalf x beta t * wardLorentzianHalf y (-gamma) t) +
        (∫ t : ℝ,
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y gamma t) +
        (∫ t : ℝ,
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y (-gamma) t) := by
    calc
      (∫ t : ℝ,
        wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t +
          wardLorentzianHalf x beta t * wardLorentzianHalf y (-gamma) t +
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y gamma t +
          wardLorentzianHalf x (-beta) t * wardLorentzianHalf y (-gamma) t) =
        ∫ t : ℝ,
          (wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t +
            wardLorentzianHalf x beta t * wardLorentzianHalf y (-gamma) t) +
          (wardLorentzianHalf x (-beta) t * wardLorentzianHalf y gamma t +
            wardLorentzianHalf x (-beta) t * wardLorentzianHalf y (-gamma) t) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          ring
      _ =
          (∫ t : ℝ,
            wardLorentzianHalf x beta t * wardLorentzianHalf y gamma t +
              wardLorentzianHalf x beta t * wardLorentzianHalf y (-gamma) t) +
          (∫ t : ℝ,
            wardLorentzianHalf x (-beta) t * wardLorentzianHalf y gamma t +
              wardLorentzianHalf x (-beta) t * wardLorentzianHalf y (-gamma) t) := by
        simpa only [Pi.add_apply] using
          MeasureTheory.integral_add (hpp.add hpm) (hmp.add hmm)
      _ = _ := by
        rw [MeasureTheory.integral_add hpp hpm,
          MeasureTheory.integral_add hmp hmm]
        ring
  rw [hsplit]
  rw [integral_wardLorentzianHalf_mul hx hy beta gamma,
    integral_wardLorentzianHalf_mul hx hy beta (-gamma),
    integral_wardLorentzianHalf_mul hx hy (-beta) gamma,
    integral_wardLorentzianHalf_mul hx hy (-beta) (-gamma)]
  ring_nf

/-- Real part of the actual Ward pair response is the reflected Lorentzian
profile with width `sigma + transverse displacement`. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_eq_reflectedProfile
    (q : XiRightUpperZeroCopy) (sigma t : ℝ) :
    (xiAntiCausalWardSchwarzPairResponse q
        ((sigma : ℂ) + Complex.I * (t : ℂ))).re =
      wardReflectedLorentzianProfile
        (sigma + (xiRightCenteredZero q.1).re)
        (xiRightCenteredZero q.1).im t := by
  rw [re_xiAntiCausalWardSchwarzPairResponse_line_eq]
  unfold wardReflectedLorentzianProfile wardLorentzianHalf
  ring_nf

/-- Cross energy of two actual Ward Schwarz pairs on one vertical line. -/
def xiWardPairRealCrossEnergyAtLine
    (sigma : ℝ) (q r : XiRightUpperZeroCopy) : ℝ :=
  ∫ t : ℝ,
    (xiAntiCausalWardSchwarzPairResponse q
      ((sigma : ℂ) + Complex.I * (t : ℂ))).re *
    (xiAntiCausalWardSchwarzPairResponse r
      ((sigma : ℂ) + Complex.I * (t : ℂ))).re

/-- Advancing both source-safe Ward widths by ten units produces exactly the
reflected annulus kernel defined above. -/
theorem xiWardPairRealCrossEnergy_fiftyOneHundredths_sub_tenShift_eq
    (q r : XiRightUpperZeroCopy) :
    xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
        xiWardPairRealCrossEnergyAtLine (1051 / 100) q r =
      8 * Real.pi * wardReflectedPairAnnulusCross
        (51 / 100 + (xiRightCenteredZero q.1).re)
        (51 / 100 + (xiRightCenteredZero r.1).re)
        (xiRightCenteredZero q.1).im
        (xiRightCenteredZero r.1).im := by
  have hq : 0 < 51 / 100 + (xiRightCenteredZero q.1).re := by
    have := xiRightCenteredZero_re_pos q.1
    norm_num
    linarith
  have hr : 0 < 51 / 100 + (xiRightCenteredZero r.1).re := by
    have := xiRightCenteredZero_re_pos r.1
    norm_num
    linarith
  have hq' : 0 < 1051 / 100 + (xiRightCenteredZero q.1).re := by linarith
  have hr' : 0 < 1051 / 100 + (xiRightCenteredZero r.1).re := by linarith
  unfold xiWardPairRealCrossEnergyAtLine
  simp_rw [re_xiAntiCausalWardSchwarzPairResponse_eq_reflectedProfile]
  rw [integral_wardReflectedLorentzianProfile_mul hq hr,
    integral_wardReflectedLorentzianProfile_mul hq' hr']
  unfold wardReflectedPairAnnulusCross wardAnnulusCrossKernel
  ring_nf

/-- Every two Ward Schwarz pairs whose positive ordinates lie in one unit
cell have a uniformly positive source-safe annulus cross energy. -/
theorem thirtyFour_pi_twentyOne_le_xiWardPairRealCrossEnergy_annulus
    (q r : XiRightUpperZeroCopy)
    (hcell : ((xiRightCenteredZero q.1).im -
      (xiRightCenteredZero r.1).im) ^ 2 ≤ 1) :
    34 * Real.pi / 21 ≤
      xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
        xiWardPairRealCrossEnergyAtLine (1051 / 100) q r := by
  have hqpos := xiRightCenteredZero_re_pos q.1
  have hrpos := xiRightCenteredZero_re_pos r.1
  have hqhi := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hrhi := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half r.1)).2
  have hcross := seventeen_eightyFour_le_wardReflectedPairAnnulusCross
    (x := 51 / 100 + (xiRightCenteredZero q.1).re)
    (y := 51 / 100 + (xiRightCenteredZero r.1).re)
    (beta := (xiRightCenteredZero q.1).im)
    (gamma := (xiRightCenteredZero r.1).im)
    (by norm_num; exact hqpos.le) (by norm_num; linarith)
    (by norm_num; exact hrpos.le) (by norm_num; linarith) hcell
  have hscaled := mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ 8 * Real.pi by positivity)
  rw [xiWardPairRealCrossEnergy_fiftyOneHundredths_sub_tenShift_eq]
  nlinarith [Real.pi_pos]

/-- **Exact three-quarters quantum.**  Restricting the ordinate diameter to
one half-unit raises every reflected-pair annulus entry to at least `3π`.
This is the same constant as the source-only HCF `3π` gate. -/
theorem three_pi_le_xiWardPairRealCrossEnergy_annulus
    (q r : XiRightUpperZeroCopy)
    (hcell : ((xiRightCenteredZero q.1).im -
      (xiRightCenteredZero r.1).im) ^ 2 ≤ 1 / 4) :
    3 * Real.pi ≤
      xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
        xiWardPairRealCrossEnergyAtLine (1051 / 100) q r := by
  have hqpos := xiRightCenteredZero_re_pos q.1
  have hrpos := xiRightCenteredZero_re_pos r.1
  have hqhi := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hrhi := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half r.1)).2
  have hcross := three_eighths_le_wardReflectedPairAnnulusCross
    (x := 51 / 100 + (xiRightCenteredZero q.1).re)
    (y := 51 / 100 + (xiRightCenteredZero r.1).re)
    (beta := (xiRightCenteredZero q.1).im)
    (gamma := (xiRightCenteredZero r.1).im)
    (by norm_num; exact hqpos.le) (by norm_num; linarith)
    (by norm_num; exact hrpos.le) (by norm_num; linarith) hcell
  have hscaled := mul_le_mul_of_nonneg_left hcross
    (show 0 ≤ 8 * Real.pi by positivity)
  rw [xiWardPairRealCrossEnergy_fiftyOneHundredths_sub_tenShift_eq]
  nlinarith [Real.pi_pos]

/-! ## Zero-independent triangular localization -/

/-- Normalized autocorrelation of a fixed half-unit height window.  It is a
translation-invariant, compactly supported replacement for choosing a cell
phase and then choosing Rademacher signs. -/
def wardHalfCellTent (delta : ℝ) : ℝ :=
  2 * max (1 / 2 - |delta|) 0

theorem wardHalfCellTent_nonneg (delta : ℝ) :
    0 ≤ wardHalfCellTent delta := by
  unfold wardHalfCellTent
  positivity

@[simp] theorem wardHalfCellTent_zero : wardHalfCellTent 0 = 1 := by
  norm_num [wardHalfCellTent]

/-- Positive tent weight forces the exact half-unit separation needed by
the `3π` annulus bound. -/
theorem sq_le_one_fourth_of_wardHalfCellTent_pos
    {delta : ℝ} (hpos : 0 < wardHalfCellTent delta) :
    delta ^ 2 ≤ 1 / 4 := by
  have hmax : 0 < max (1 / 2 - |delta|) 0 := by
    unfold wardHalfCellTent at hpos
    nlinarith
  have habs : |delta| < 1 / 2 := by
    by_contra h
    have hle : 1 / 2 - |delta| ≤ 0 := by linarith
    rw [max_eq_right hle] at hmax
    linarith
  have hsq := (sq_lt_sq₀ (abs_nonneg delta)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 habs
  rw [sq_abs] at hsq
  norm_num at hsq ⊢
  exact hsq.le

/-- The tent is literally a source-independent interval autocorrelation,
not a divisor-selected cutoff. -/
theorem wardHalfCellTent_eq_intervalAutocorrelation (delta : ℝ) :
    wardHalfCellTent delta =
      2 * ∫ u : ℝ,
        (Set.Icc (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) (u + delta) *
          (Set.Icc (0 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) u := by
  rw [integral_indicator_Icc_shift_mul]
  simp only [sub_zero]
  rfl

/-- Contribution of one ordered Schwarz-pair pair to the fixed triangularly
localized Ward annulus. -/
def xiWardTriangularLocalizedAnnulusPair
    (q r : XiRightUpperZeroCopy) : ℝ :=
  wardHalfCellTent
      ((xiRightCenteredZero q.1).im - (xiRightCenteredZero r.1).im) *
    (xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
      xiWardPairRealCrossEnergyAtLine (1051 / 100) q r)

/-- Every localized ordered-pair contribution is nonnegative.  Outside the
half-unit band the tent vanishes; inside it the Ward annulus is at least
`3π`. -/
theorem xiWardTriangularLocalizedAnnulusPair_nonneg
    (q r : XiRightUpperZeroCopy) :
    0 ≤ xiWardTriangularLocalizedAnnulusPair q r := by
  let delta :=
    (xiRightCenteredZero q.1).im - (xiRightCenteredZero r.1).im
  by_cases htent : wardHalfCellTent delta = 0
  · simp [xiWardTriangularLocalizedAnnulusPair, delta, htent]
  · have htentNonneg := wardHalfCellTent_nonneg delta
    have htentPos : 0 < wardHalfCellTent delta := lt_of_le_of_ne
      htentNonneg (Ne.symm htent)
    have hcross := three_pi_le_xiWardPairRealCrossEnergy_annulus q r
      (sq_le_one_fourth_of_wardHalfCellTent_pos htentPos)
    unfold xiWardTriangularLocalizedAnnulusPair
    exact mul_nonneg htentNonneg ((by positivity : 0 ≤ 3 * Real.pi).trans hcross)

/-- Fixed triangular pair statistic on a finite strict-right multiplicity
packet.  It contains no cell map, phase, or selected signs. -/
def xiWardTriangularLocalizedAnnulusEnergy
    (S : Finset XiRightUpperZeroCopy) : ℝ :=
  ∑ q ∈ S, ∑ r ∈ S, xiWardTriangularLocalizedAnnulusPair q r

/-- **Deterministic `3π` receiver.**  Fixed half-window autocorrelation
charges every strict-right multiplicity copy by `3π`; all off-diagonal terms
are nonnegative.  The remaining producer is now one fixed triangular
pole--Gamma--von-Mangoldt pair evaluation, with no divisor-dependent choice. -/
theorem card_mul_three_pi_le_xiWardTriangularLocalizedAnnulusEnergy
    (S : Finset XiRightUpperZeroCopy) :
    (S.card : ℝ) * (3 * Real.pi) ≤
      xiWardTriangularLocalizedAnnulusEnergy S := by
  rw [show (S.card : ℝ) * (3 * Real.pi) =
      ∑ _q ∈ S, 3 * Real.pi by simp]
  unfold xiWardTriangularLocalizedAnnulusEnergy
  apply Finset.sum_le_sum
  intro q hq
  have hnonneg : ∀ r ∈ S,
      0 ≤ xiWardTriangularLocalizedAnnulusPair q r := by
    intro r hr
    exact xiWardTriangularLocalizedAnnulusPair_nonneg q r
  have hdiag : 3 * Real.pi ≤ xiWardTriangularLocalizedAnnulusPair q q := by
    rw [xiWardTriangularLocalizedAnnulusPair]
    simp only [sub_self, wardHalfCellTent_zero, one_mul]
    exact three_pi_le_xiWardPairRealCrossEnergy_annulus q q (by norm_num)
  exact hdiag.trans (Finset.single_le_sum hnonneg hq)

/-! ## Exact cell-sign diagonalization -/

/-- Rademacher sign attached to one source-independent height cell. -/
def wardCellSign
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (epsilon : κ → Bool) (c : κ) : ℝ :=
  GaloisForLFunctions.HTGeometry.lbitWalshCharacterReal {c} epsilon

/-- Independent cell signs are orthogonal. -/
theorem sum_wardCellSign_mul
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c d : κ) :
    (∑ epsilon : κ → Bool, wardCellSign epsilon c * wardCellSign epsilon d) =
      if c = d then (2 : ℝ) ^ Fintype.card κ else 0 := by
  simpa only [wardCellSign, Finset.singleton_inj] using
    (GaloisForLFunctions.HTGeometry.sum_lbitWalshCharacterReal_mul
      ({c} : Finset κ) ({d} : Finset κ))

/-- Quadratic annulus energy after assigning one sign to every height cell. -/
def wardCellSignedQuadratic
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (S : Finset ι) (cell : ι → κ) (K : ι → ι → ℝ)
    (epsilon : κ → Bool) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S,
    wardCellSign epsilon (cell i) * wardCellSign epsilon (cell j) * K i j

/-- The unsigned block-diagonal energy retained after cell randomization. -/
def wardCellDiagonalQuadratic
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (S : Finset ι) (cell : ι → κ) (K : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, if cell i = cell j then K i j else 0

/-- A nonnegative within-cell kernel retains at least one diagonal quantum
per packet element. -/
theorem card_mul_le_wardCellDiagonalQuadratic
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (S : Finset ι) (cell : ι → κ) (K : ι → ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hK : ∀ i ∈ S, ∀ j ∈ S, cell i = cell j → c ≤ K i j) :
    (S.card : ℝ) * c ≤ wardCellDiagonalQuadratic S cell K := by
  unfold wardCellDiagonalQuadratic
  rw [show (S.card : ℝ) * c = ∑ _i ∈ S, c by simp]
  apply Finset.sum_le_sum
  intro i hi
  have hnonneg : ∀ j ∈ S,
      0 ≤ if cell i = cell j then K i j else 0 := by
    intro j hj
    by_cases hij : cell i = cell j
    · rw [if_pos hij]
      exact hc.trans (hK i hi j hj hij)
    · rw [if_neg hij]
  have hsingle := Finset.single_le_sum hnonneg hi
  exact (hK i hi i hi rfl).trans (by simpa using hsingle)

/-- Exact Rademacher diagonalization: averaging all cell signs deletes every
inter-cell cross term and retains every within-cell term with multiplicity
`2^#cells`. -/
theorem sum_wardCellSignedQuadratic_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (S : Finset ι) (cell : ι → κ) (K : ι → ι → ℝ) :
    (∑ epsilon : κ → Bool,
      wardCellSignedQuadratic S cell K epsilon) =
      (2 : ℝ) ^ Fintype.card κ * wardCellDiagonalQuadratic S cell K := by
  classical
  unfold wardCellSignedQuadratic wardCellDiagonalQuadratic
  rw [show (∑ epsilon : κ → Bool,
      ∑ i ∈ S, ∑ j ∈ S,
        wardCellSign epsilon (cell i) * wardCellSign epsilon (cell j) * K i j) =
      ∑ i ∈ S, ∑ j ∈ S, ∑ epsilon : κ → Bool,
        wardCellSign epsilon (cell i) * wardCellSign epsilon (cell j) * K i j by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_comm]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← Finset.sum_mul, sum_wardCellSign_mul]
  by_cases hij : cell i = cell j
  · rw [if_pos hij, if_pos hij]
  · rw [if_neg hij, if_neg hij]
    ring

/-- Some deterministic cell signing attains at least the block-diagonal
energy.  Randomization is only a finite-dimensional proof device.  A source
application must still evaluate or select this fixed sign family from source
energies rather than from a divisor packet. -/
theorem exists_wardCellSignedQuadratic_ge_diagonal
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]
    (S : Finset ι) (cell : ι → κ) (K : ι → ι → ℝ) :
    ∃ epsilon : κ → Bool,
      wardCellDiagonalQuadratic S cell K ≤
        wardCellSignedQuadratic S cell K epsilon := by
  classical
  by_contra h
  push Not at h
  have hlt :
      (∑ epsilon : κ → Bool,
        wardCellSignedQuadratic S cell K epsilon) <
      ∑ _epsilon : κ → Bool, wardCellDiagonalQuadratic S cell K :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun epsilon _hepsilon ↦ h epsilon)
  rw [sum_wardCellSignedQuadratic_eq] at hlt
  have hcard : Fintype.card (κ → Bool) = 2 ^ Fintype.card κ := by
    rw [Fintype.card_eq_nat_card, Nat.card_fun]
    norm_num [Nat.card_eq_fintype_card]
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at hlt
  norm_num at hlt

/-! ## Finite source-safe randomized receiver -/

/-- Cell-signed ten-unit Ward annulus energy of a finite strict-right packet. -/
def xiWardCellSignedAnnulusEnergy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset XiRightUpperZeroCopy)
    (cell : XiRightUpperZeroCopy → κ) (epsilon : κ → Bool) : ℝ :=
  wardCellSignedQuadratic S cell
    (fun q r =>
      xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
        xiWardPairRealCrossEnergyAtLine (1051 / 100) q r)
    epsilon

/-- **Cell-randomized multiplicity receiver.**  If every pair assigned to
one cell has ordinate separation at most one, a cell-level signing exists
whose source-safe Ward annulus energy charges every strict-right multiplicity
copy by `34π/21`.  The sign is constant on a cell, not attached per zero;
source-side selection remains a separate producer obligation. -/
theorem exists_xiWardCellSignedAnnulusEnergy_card_lower
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset XiRightUpperZeroCopy)
    (cell : XiRightUpperZeroCopy → κ)
    (hcell : ∀ q ∈ S, ∀ r ∈ S, cell q = cell r →
      ((xiRightCenteredZero q.1).im -
        (xiRightCenteredZero r.1).im) ^ 2 ≤ 1) :
    ∃ epsilon : κ → Bool,
      (S.card : ℝ) * (34 * Real.pi / 21) ≤
        xiWardCellSignedAnnulusEnergy S cell epsilon := by
  let K : XiRightUpperZeroCopy → XiRightUpperZeroCopy → ℝ := fun q r =>
    xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
      xiWardPairRealCrossEnergyAtLine (1051 / 100) q r
  have hc : 0 ≤ 34 * Real.pi / 21 := by positivity
  have hK : ∀ q ∈ S, ∀ r ∈ S, cell q = cell r →
      34 * Real.pi / 21 ≤ K q r := by
    intro q hq r hr hqr
    exact thirtyFour_pi_twentyOne_le_xiWardPairRealCrossEnergy_annulus
      q r (hcell q hq r hr hqr)
  have hdiag :
      (S.card : ℝ) * (34 * Real.pi / 21) ≤
        wardCellDiagonalQuadratic S cell K :=
    card_mul_le_wardCellDiagonalQuadratic S cell K hc hK
  obtain ⟨epsilon, hepsilon⟩ :=
    exists_wardCellSignedQuadratic_ge_diagonal S cell K
  refine ⟨epsilon, hdiag.trans ?_⟩
  simpa only [xiWardCellSignedAnnulusEnergy, K] using hepsilon

/-- **Threshold-matched cell-randomized receiver.**  Half-unit cells produce
the full `3π` charge per strict-right multiplicity copy.  This eliminates the
constant loss in the cell route: only source-first realization and budgeting
of the finite sign family remain. -/
theorem exists_xiWardCellSignedAnnulusEnergy_threePi_card_lower
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Finset XiRightUpperZeroCopy)
    (cell : XiRightUpperZeroCopy → κ)
    (hcell : ∀ q ∈ S, ∀ r ∈ S, cell q = cell r →
      ((xiRightCenteredZero q.1).im -
        (xiRightCenteredZero r.1).im) ^ 2 ≤ 1 / 4) :
    ∃ epsilon : κ → Bool,
      (S.card : ℝ) * (3 * Real.pi) ≤
        xiWardCellSignedAnnulusEnergy S cell epsilon := by
  let K : XiRightUpperZeroCopy → XiRightUpperZeroCopy → ℝ := fun q r =>
    xiWardPairRealCrossEnergyAtLine (51 / 100) q r -
      xiWardPairRealCrossEnergyAtLine (1051 / 100) q r
  have hc : 0 ≤ 3 * Real.pi := by positivity
  have hK : ∀ q ∈ S, ∀ r ∈ S, cell q = cell r →
      3 * Real.pi ≤ K q r := by
    intro q hq r hr hqr
    exact three_pi_le_xiWardPairRealCrossEnergy_annulus
      q r (hcell q hq r hr hqr)
  have hdiag :
      (S.card : ℝ) * (3 * Real.pi) ≤
        wardCellDiagonalQuadratic S cell K :=
    card_mul_le_wardCellDiagonalQuadratic S cell K hc hK
  obtain ⟨epsilon, hepsilon⟩ :=
    exists_wardCellSignedQuadratic_ge_diagonal S cell K
  refine ⟨epsilon, hdiag.trans ?_⟩
  simpa only [xiWardCellSignedAnnulusEnergy, K] using hepsilon

end

end RHTower
