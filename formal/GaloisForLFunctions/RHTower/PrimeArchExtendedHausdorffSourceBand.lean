import GaloisForLFunctions.RHTower.PrimeArchEndpointHausdorffTemperatureMaster
import GaloisForLFunctions.RHTower.XiFourthTraceExtendedCriticalLineBand

/-!
# Extended endpoint Hausdorff source band

The fourth reciprocal-trace source budget rules out every off-critical Xi zero below squared
ordinate `2365 / 16`.  Combined with the open critical strip, this reduces the squared transverse
orientation of every reciprocal-square atom from `1 / 84` to `1 / 147` of its squared real part.

The resulting opposite-phase sector proves the endpoint-calibrated Hausdorff rectangle
`k ≤ 18`, `r ≤ 57` unconditionally.  Thus 1102 indexed inequalities are removed from the
RH-equivalent endpoint tail.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The fourth-trace critical-line band reduces every reciprocal-square transverse square to at
most `1 / 147` of its positive real square. -/
theorem xiThermalOrientationTerm_le_one_over_oneHundredFortySeven_node_sq
    (q : XiZeroCopy) :
    (xiZeroCopyReciprocalSquare q).im ^ 2 ≤
      (1 / 147 : ℝ) * xiThermalNode q ^ 2 := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [xiZeroCopyReciprocalSquare_im_formula, hoff]
    norm_num
    positivity
  · let u : ℝ := ((q.1 : ℂ).re - 1 / 2) ^ 2
    let v : ℝ := (q.1 : ℂ).im ^ 2
    let D : ℝ := (u + v) ^ 2
    have hstrip := xi_divisor_support_re_mem_open_unit q.1
    have hu0 : 0 ≤ u := by dsimp only [u]; positivity
    have hu : u < 1 / 4 := by
      dsimp only [u]
      nlinarith [mul_pos hstrip.1 (sub_pos.mpr hstrip.2)]
    have hv : (2365 / 16 : ℝ) ≤ v := by
      apply le_of_not_gt
      intro hvlt
      exact hoff (xiZeroCopy_re_eq_half_of_im_sq_lt_2365_over_16 q (by
        simpa only [v] using hvlt))
    have hv0 : 0 < v := by nlinarith
    have h590 : 590 * u < v := by nlinarith
    have hprod : 0 ≤ v * (v - 590 * u) :=
      mul_nonneg hv0.le (sub_nonneg.mpr h590.le)
    have hcore : 4 * u * v ≤ (1 / 147 : ℝ) * (v - u) ^ 2 := by
      have hid :
          (v - u) ^ 2 - 147 * (4 * u * v) =
            v * (v - 590 * u) + u ^ 2 := by
        ring
      nlinarith [sq_nonneg u]
    have hD : 0 < D := by dsimp only [D]; positivity
    rw [xiThermalNode, xiZeroCopyReciprocalSquare_re_formula,
      xiZeroCopyReciprocalSquare_im_formula]
    change (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im /
          (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2 ≤
      (1 / 147 : ℝ) *
        (((q.1 : ℂ).im ^ 2 - ((q.1 : ℂ).re - 1 / 2) ^ 2) /
          (((q.1 : ℂ).re - 1 / 2) ^ 2 + (q.1 : ℂ).im ^ 2) ^ 2) ^ 2
    rw [show ((q.1 : ℂ).re - 1 / 2) ^ 2 = u by rfl,
      show (q.1 : ℂ).im ^ 2 = v by rfl,
      show (u + v) ^ 2 = D by rfl]
    rw [div_pow, div_pow]
    rw [show (1 / 147 : ℝ) * ((v - u) ^ 2 / D ^ 2) =
        ((1 / 147 : ℝ) * (v - u) ^ 2) / D ^ 2 by ring]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hD)).2
    calc
      (2 * ((q.1 : ℂ).re - 1 / 2) * (q.1 : ℂ).im) ^ 2 =
          4 * u * v := by
        dsimp only [u, v]
        ring
      _ ≤ (1 / 147 : ℝ) * (v - u) ^ 2 := hcore

/-- Rational square-root form of the improved reciprocal-square sector. -/
theorem twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re
    (q : XiZeroCopy) :
    (121 / 10 : ℝ) * |(xiZeroCopyReciprocalSquare q).im| ≤
      (xiZeroCopyReciprocalSquare q).re := by
  let z := xiZeroCopyReciprocalSquare q
  have hre : 0 ≤ z.re := by
    simpa only [z, xiThermalNode] using (xiThermalNode_pos q).le
  have hsq : z.im ^ 2 ≤ (1 / 147 : ℝ) * z.re ^ 2 := by
    simpa only [z, xiThermalNode] using
      xiThermalOrientationTerm_le_one_over_oneHundredFortySeven_node_sq q
  apply (sq_le_sq₀ (mul_nonneg (by norm_num) (abs_nonneg _)) hre).mp
  rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg z.im, sq_nonneg z.re]

private theorem re_pow_mul_pow_nonneg_of_extended_opposite_phase_rectangle
    (z w : ℂ) (p r : ℕ)
    (hzre : 0 < z.re) (hwre : 0 < w.re)
    (hwim : w.im = -z.im)
    (hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re)
    (hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re)
    (hp : p ≤ 19) (hr : r ≤ 57) :
    0 ≤ (z ^ p * w ^ r).re := by
  have hzarg : |z.arg| ≤ (10 / 121 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hzre (by nlinarith)
  have hwarg : |w.arg| ≤ (10 / 363 : ℝ) :=
    abs_arg_le_of_re_pos_for_scaledHausdorff hwre (by nlinarith)
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hr0 : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hpR : (p : ℝ) ≤ 19 := by exact_mod_cast hp
  have hrR : (r : ℝ) ≤ 57 := by exact_mod_cast hr
  let x : ℝ := (p : ℝ) * z.arg
  let y : ℝ := (r : ℝ) * w.arg
  let M : ℝ := 190 / 121
  have hx : |x| ≤ M := by
    calc
      |x| = (p : ℝ) * |z.arg| := by
        simp only [x, abs_mul, abs_of_nonneg hp0]
      _ ≤ (p : ℝ) * (10 / 121 : ℝ) :=
        mul_le_mul_of_nonneg_left hzarg hp0
      _ ≤ M := by dsimp only [M]; nlinarith
  have hy : |y| ≤ M := by
    calc
      |y| = (r : ℝ) * |w.arg| := by
        simp only [y, abs_mul, abs_of_nonneg hr0]
      _ ≤ (r : ℝ) * (10 / 363 : ℝ) :=
        mul_le_mul_of_nonneg_left hwarg hr0
      _ ≤ M := by dsimp only [M]; nlinarith
  have hangle : |x + y| ≤ M := by
    rw [abs_le]
    have hxI := abs_le.mp hx
    have hyI := abs_le.mp hy
    by_cases hzim : 0 ≤ z.im
    · have hzarg0 : 0 ≤ z.arg := Complex.arg_nonneg_iff.mpr hzim
      have hwim0 : w.im ≤ 0 := by rw [hwim]; linarith
      have hwarg0 : w.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hwre]
        have hratio : 0 ≤ -(w.im / w.re) := by
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hwim0 hwre.le)
        have h := Real.arctan_nonneg.mpr hratio
        rw [Real.arctan_neg] at h
        linarith
      have hx0 : 0 ≤ x := mul_nonneg hp0 hzarg0
      have hy0 : y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0 hwarg0
      constructor
      · exact hyI.1.trans (by linarith)
      · exact (by linarith : x + y ≤ x).trans hxI.2
    · have hzim0 : z.im ≤ 0 := le_of_not_ge hzim
      have hzarg0 : z.arg ≤ 0 := by
        rw [arg_eq_arctan_of_re_pos hzre]
        have hratio : 0 ≤ -(z.im / z.re) := by
          exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hzim0 hzre.le)
        have h := Real.arctan_nonneg.mpr hratio
        rw [Real.arctan_neg] at h
        linarith
      have hwim0 : 0 ≤ w.im := by rw [hwim]; linarith
      have hwarg0 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hwim0
      have hx0 : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 hzarg0
      have hy0 : 0 ≤ y := mul_nonneg hr0 hwarg0
      constructor
      · exact hxI.1.trans (by linarith)
      · exact (by linarith : x + y ≤ y).trans hyI.2
  have hpi : M < Real.pi / 2 := by
    dsimp only [M]
    nlinarith [Real.pi_gt_d20]
  have hangleMem : x + y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hangle
    exact ⟨(neg_le_neg hpi.le).trans hangle.1, hangle.2.trans hpi.le⟩
  rw [pow_mul_pow_re_eq_norm_cos]
  change 0 ≤ ‖z‖ ^ p * ‖w‖ ^ r * Real.cos (x + y)
  exact mul_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg z) p) (pow_nonneg (norm_nonneg w) r))
    (Real.cos_nonneg_of_mem_Icc hangleMem)

/-- Every reciprocal-square Xi atom is nonnegative on the enlarged endpoint rectangle
`k ≤ 18`, `r ≤ 57`. -/
theorem re_xiCentral_scaledBasis_extendedRectangle_nonneg
    (q : XiZeroCopy) (k r : ℕ) (hk : k ≤ 18) (hr : r ≤ 57) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ (k + 1) *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  have hzre : 0 < z.re := by
    simpa only [z, xiThermalNode] using xiThermalNode_pos q
  have hzre0 : 0 ≤ z.re := hzre.le
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hzReal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hwReal : w = ((R - z.re : ℝ) : ℂ) := by
      dsimp only [w]
      rw [hzReal]
      norm_num
    have hzleR : z.re ≤ R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q
    change 0 ≤ (z ^ (k + 1) * w ^ r).re
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre0 (k + 1))
      (pow_nonneg (sub_nonneg.mpr hzleR) r)
  · have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hon
    have hwre : 0 < w.re := by
      dsimp only [w]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re := by
      simpa only [z] using
        twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re q
    have hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re := by
      dsimp only [w]
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hwim : w.im = -z.im := by
      dsimp only [w]
      simp
    have hp : k + 1 ≤ 19 := by omega
    change 0 ≤ (z ^ (k + 1) * w ^ r).re
    exact re_pow_mul_pow_nonneg_of_extended_opposite_phase_rectangle
      z w (k + 1) r hzre hwre hwim hzsector hwsector hp hr

/-- The `19 × 58` endpoint Hausdorff rectangle is unconditionally nonnegative. -/
theorem scaledPrimeArchEndpointHausdorffDifference_extendedRectangle_nonnegative
    (k r : ℕ) (hk : k ≤ 18) (hr : r ≤ 57) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius k r)]
  apply tsum_nonneg
  intro q
  exact re_xiCentral_scaledBasis_extendedRectangle_nonneg q k r hk hr

/-- Weighted form of the extended source band. -/
theorem scaledPrimeArchEndpointHausdorffDifference_weightedDegree_le_fiftyFour_nonnegative
    (k r : ℕ) (hweight : 3 * k + r ≤ 54) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r := by
  exact scaledPrimeArchEndpointHausdorffDifference_extendedRectangle_nonnegative
    k r (by omega) (by omega)

/-- Remaining endpoint carrier after the enlarged source-derived rectangle is discharged. -/
def PrimeArchEndpointExtendedHausdorffTailNonnegative : Prop :=
  ∀ k r : ℕ, 18 < k ∨ 57 < r →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r

/-- The previous endpoint-tail interface is exactly its smaller extended tail. -/
theorem primeArchEndpointHausdorffTailNonnegative_iff_extendedTailNonnegative :
    PrimeArchEndpointHausdorffTailNonnegative ↔
      PrimeArchEndpointExtendedHausdorffTailNonnegative := by
  constructor
  · intro hold k r htail
    exact hold k r (by omega)
  · intro hext
    apply primeArchEndpointHausdorffTailNonnegative_iff_full.mpr
    intro k r
    by_cases hk : k ≤ 18
    · by_cases hr : r ≤ 57
      · exact
          scaledPrimeArchEndpointHausdorffDifference_extendedRectangle_nonnegative k r hk hr
      · exact hext k r (Or.inr (by omega))
    · exact hext k r (Or.inl (by omega))

/-- The reduced extended endpoint tail remains precisely the RH interface. -/
theorem primeArchEndpointExtendedHausdorffTailNonnegative_iff_riemannHypothesis :
    PrimeArchEndpointExtendedHausdorffTailNonnegative ↔ RiemannHypothesis :=
  primeArchEndpointHausdorffTailNonnegative_iff_extendedTailNonnegative.symm.trans
    primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis

/-- The prime--polar abscissa interface needs only the reduced extended tail. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_extendedHausdorffTailNonnegative
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔
      PrimeArchEndpointExtendedHausdorffTailNonnegative :=
  (rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative
    hL hN).trans
      primeArchEndpointHausdorffTailNonnegative_iff_extendedTailNonnegative

/-- Finite KMS/Wightman local closure needs only the reduced extended tail. -/
theorem primeArchEndpointExtendedHausdorffTailNonnegative_iff_finiteKMSLocalMomentClosure :
    PrimeArchEndpointExtendedHausdorffTailNonnegative ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure :=
  primeArchEndpointExtendedHausdorffTailNonnegative_iff_riemannHypothesis.trans
    primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis.symm

/-- The enlarged rectangle contains exactly 1102 indexed inequalities. -/
theorem primeArchEndpointExtendedHausdorffRectangle_cardinality :
    19 * 58 = 1102 := by
  norm_num

end

end RHTower
