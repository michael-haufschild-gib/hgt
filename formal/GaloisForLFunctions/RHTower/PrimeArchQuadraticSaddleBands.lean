import GaloisForLFunctions.BiScaleUncertainty.HausdorffSaddleScale
import GaloisForLFunctions.RHTower.PrimeArchHausdorffFixedOrderLargeShiftPositivity
import GaloisForLFunctions.RHTower.XiZeroCountLocalCeiling

/-!
# Unconditional positive saddle bands at quadratic Hausdorff scale

At radius one, the actual atom is `x^(k+1)(1-x)^r`. Its two phases cancel
near ordinate `sqrt(r/(k+1))`. A fixed-width band there retains half its
absolute mass once `r` is a sufficiently large constant times `(k+1)^2`.
The logarithmic Riemann--von Mangoldt remainder supplies a nonempty band.
The complementary spectral contribution is not asserted to be positive.
-/

open Complex Filter Topology
open scoped BigOperators
open GaloisForLFunctions.BiScaleUncertainty

namespace RHTower

noncomputable section

/-- The real reciprocal-square atom is squeezed between neighboring reciprocal squares. -/
theorem xiThermalNode_ordinate_reciprocal_bounds (q : XiZeroCopy) :
    1 / ((xiSpectralPoint q).re ^ 2 + 1) ≤ xiThermalNode q ∧
      xiThermalNode q ≤ 1 / (xiSpectralPoint q).re ^ 2 := by
  let A : ℝ := (xiSpectralPoint q).re ^ 2
  let B : ℝ := (xiSpectralPoint q).im ^ 2
  have hA : 41 / 2 ≤ A := xiSpectralPoint_re_sq_ge q
  have hB : B < 1 / 4 := xiSpectralPoint_im_sq_lt q
  have hA0 : 0 < A := by linarith
  have hB0 : 0 ≤ B := sq_nonneg _
  have hN : Complex.normSq (xiSpectralPoint q) = A + B := normSq_xiSpectralPoint_eq q
  have hlam : xiThermalNode q = (A - B) / (A + B) ^ 2 := by
    rw [xiThermalNode_eq_re, xiZeroCopyReciprocalSquare_re, hN]
  have hAB0 : 0 < A + B := by positivity
  constructor
  · rw [hlam, div_le_div_iff₀ (by positivity) (pow_pos hAB0 2)]
    have hAB : A * B ≤ A / 4 := by
      nlinarith [mul_nonneg hA0.le (show 0 ≤ 1 / 4 - B by linarith)]
    have hB2 : B ^ 2 ≤ B / 4 := by
      nlinarith [mul_nonneg hB0 (show 0 ≤ 1 / 4 - B by linarith)]
    nlinarith
  · calc
      xiThermalNode q ≤ 1 / Complex.normSq (xiSpectralPoint q) :=
        xiThermalNode_le_inv_normSq q
      _ ≤ 1 / A := by
        rw [hN]
        exact one_div_le_one_div_of_le hA0 (by linarith)

/-- The endpoint-complement slope at radius one has a sharp ordinate comparison. -/
theorem xiThermalComplementSlope_bounds (q : XiZeroCopy) :
    xiThermalNode q < 1 ∧
      1 / (xiSpectralPoint q).re ^ 2 ≤ xiThermalNode q / (1 - xiThermalNode q) ∧
      xiThermalNode q / (1 - xiThermalNode q) ≤
        1 / ((xiSpectralPoint q).re ^ 2 - 1) := by
  obtain ⟨hL, hU⟩ := xiThermalNode_ordinate_reciprocal_bounds q
  have hu : 41 / 2 ≤ (xiSpectralPoint q).re ^ 2 := xiSpectralPoint_re_sq_ge q
  have hu0 : 0 < (xiSpectralPoint q).re ^ 2 := by linarith
  have hlam1 : xiThermalNode q < 1 := by
    have h := (le_div_iff₀ hu0).mp hU
    nlinarith [xiThermalNode_pos q]
  have hden : 0 < 1 - xiThermalNode q := by linarith
  refine ⟨hlam1, ?_, ?_⟩
  · have h := (div_le_iff₀ (show 0 < (xiSpectralPoint q).re ^ 2 + 1 by positivity)).mp hL
    rw [div_le_div_iff₀ hu0 hden]
    nlinarith
  · have h := (le_div_iff₀ hu0).mp hU
    rw [div_le_div_iff₀ hden (show 0 < (xiSpectralPoint q).re ^ 2 - 1 by linarith)]
    nlinarith

/-- Every actual atom in the saddle band retains half its absolute mass at quadratic scale. -/
theorem half_norm_hausdorffAtomTerm_le_re_of_quadratic_band
    (k r : ℕ) {T H : ℝ} (hT : 4 ≤ T) (hH : 1 ≤ H) (hHT : H ≤ T)
    (hr : (r : ℝ) = ((k + 1 : ℕ) : ℝ) * T ^ 2)
    (hscale : 32 * ((k + 1 : ℕ) : ℝ) * H ≤ T ^ 2)
    {q : XiZeroCopy} (hqL : T ≤ |(xiSpectralPoint q).re|)
    (hqU : |(xiSpectralPoint q).re| ≤ T + H) :
    1 / 2 * ‖hausdorffAtomTerm 1 k r q‖ ≤ (hausdorffAtomTerm 1 k r q).re := by
  let lam : ℝ := xiThermalNode q
  let a : ℝ := lam / (1 - lam)
  let τ : ℝ := (xiZeroCopyReciprocalSquare q).im / lam
  have hlam : 0 < lam := xiThermalNode_pos q
  obtain ⟨hlam1, haL, haU⟩ := xiThermalComplementSlope_bounds q
  have hden : 0 < 1 - lam := by dsimp only [lam]; linarith
  have haL' : 1 / |(xiSpectralPoint q).re| ^ 2 ≤ a := by simpa only [sq_abs] using haL
  have haU' : a ≤ 1 / (|(xiSpectralPoint q).re| ^ 2 - 1) := by
    simpa only [sq_abs] using haU
  obtain ⟨ha0, ha1, hra, hbalance⟩ := hausdorff_saddle_slope_bounds
    (Nat.cast_nonneg (k + 1)) hT hH hHT hqL hqU hr haL' haU'
  have hτ : |τ| ≤ 2 / T := by
    have h := abs_im_le_of_ordinate_ge (by linarith : 0 < T) hqL
    dsimp only [τ]
    rw [abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
    exact h
  have hbudget := signedPowerPhaseBudget_le_of_saddle_bounds (k + 1) r
    hT hH hscale ha0 ha1 hra hbalance hτ
  have hphase := half_norm_le_re_compensated_power (k + 1) r
    (show signedPowerPhaseBudget (k + 1) r τ (a * τ) ≤ 1 by linarith)
  have hσ : (xiZeroCopyReciprocalSquare q).im / (1 - xiThermalNode q) = a * τ := by
    dsimp only [a, τ, lam]
    field_simp [(xiThermalNode_pos q).ne', (sub_pos.mpr hlam1).ne']
  rw [hausdorffAtomTerm_eq_scale_mul_phase 1 k r q hlam1, hσ]
  let c : ℝ := xiThermalNode q ^ (k + 1) * (1 - xiThermalNode q) ^ r
  have hc : 0 ≤ c := mul_nonneg (pow_nonneg hlam.le _) (pow_nonneg hden.le _)
  change 1 / 2 * ‖(c : ℂ) * _‖ ≤ ((c : ℂ) * _).re
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc,
    Complex.re_ofReal_mul]
  nlinarith [mul_le_mul_of_nonneg_left hphase hc]

/-- Radius-one actual atoms never vanish. -/
theorem hausdorffAtomTerm_one_ne_zero (k r : ℕ) (q : XiZeroCopy) :
    hausdorffAtomTerm 1 k r q ≠ 0 := by
  have hx : xiZeroCopyReciprocalSquare q ≠ 0 := by
    intro h
    have hlam := xiThermalNode_pos q
    rw [xiThermalNode_eq_re, h] at hlam
    norm_num at hlam
  have hy : (1 : ℂ) - xiZeroCopyReciprocalSquare q ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hlam1 := (xiThermalComplementSlope_bounds q).1
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    rw [xiThermalNode_eq_re] at hlam1
    linarith
  exact mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hy)

/-- The positive band retains half its total variation; no cancellation is lost in summation. -/
theorem half_sum_norm_hausdorffAtomTerm_le_quadratic_band_sum
    (k r : ℕ) {T H : ℝ} (hT : 4 ≤ T) (hH : 1 ≤ H) (hHT : H ≤ T)
    (hr : (r : ℝ) = ((k + 1 : ℕ) : ℝ) * T ^ 2)
    (hscale : 32 * ((k + 1 : ℕ) : ℝ) * H ≤ T ^ 2) :
    1 / 2 * ∑ q ∈ xiCopiesBand T (T + H), ‖hausdorffAtomTerm 1 k r q‖ ≤
      ∑ q ∈ xiCopiesBand T (T + H), (hausdorffAtomTerm 1 k r q).re := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨hqL, hqU⟩ := mem_xiCopiesBand.mp hq
  apply half_norm_hausdorffAtomTerm_le_re_of_quadratic_band k r hT hH hHT hr hscale
  · simpa only [xiSpectralPoint_re_eq_ordinate'] using hqL.le
  · simpa only [xiSpectralPoint_re_eq_ordinate'] using hqU

/-- The logarithmic counting remainder supplies a nonempty fixed-width band at every large height. -/
theorem exists_fixed_width_xiCopiesBand_nonempty :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ S : ℝ, 4 ≤ S ∧ H ≤ S ∧
      ∀ T : ℝ, S ≤ T → (xiCopiesBand T (T + H)).Nonempty := by
  classical
  obtain ⟨C, hC, T₀, hT₀, hrem⟩ := exists_xiZeroCount_routeKSmoothRVMCount_log_remainder
  let H : ℝ := 16 * Real.pi * (C + 1)
  have hH : 1 ≤ H := by dsimp only [H]; nlinarith [Real.pi_gt_three]
  let S : ℝ := max T₀ (max H (max 4 (routeKRVMBase ^ 2)))
  have hS4 : 4 ≤ S :=
    (le_max_left 4 _).trans ((le_max_right H _).trans (le_max_right T₀ _))
  have hHS : H ≤ S := (le_max_left H _).trans (le_max_right T₀ _)
  refine ⟨H, hH, S, hS4, hHS, fun T hST => ?_⟩
  have hT4 : 4 ≤ T := hS4.trans hST
  have hT0 : 0 < T := by linarith
  have hHT : H ≤ T := hHS.trans hST
  have hT₀T : T₀ ≤ T := (le_max_left T₀ _).trans hST
  have hbaseT : routeKRVMBase ^ 2 ≤ T :=
    (le_max_right 4 _).trans ((le_max_right H _).trans ((le_max_right T₀ _).trans hST))
  have hTH0 : 0 < T + H := by linarith
  have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogmon : Real.log T ≤ Real.log (T + H) := Real.log_le_log hT0 (by linarith)
  have hlogUpper : Real.log (T + H) ≤ 2 * Real.log T := by
    have hh : T + H ≤ T ^ 2 := by nlinarith
    have hh' := Real.log_le_log hTH0 hh
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh'
  have hlogBase : 2 * Real.log routeKRVMBase ≤ Real.log T := by
    have hh := Real.log_le_log (pow_pos routeKRVMBase_pos 2) hbaseT
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hmain : H / (4 * Real.pi) * Real.log T ≤
      routeKSmoothRVMCount (T + H) - routeKSmoothRVMCount T := by
    rw [routeKSmoothRVMCount_sub_eq hT0 hTH0, le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
    have hmon := mul_le_mul_of_nonneg_left hlogmon hTH0.le
    have hb := mul_le_mul_of_nonneg_left hlogBase (by linarith : 0 ≤ H)
    have heq : H / (4 * Real.pi) * Real.log T * (2 * Real.pi) = H * Real.log T / 2 := by
      field_simp
      ring
    rw [heq]
    nlinarith
  have hremL := (abs_le.mp (hrem T hT₀T)).2
  have hremU := (abs_le.mp (hrem (T + H) (by linarith))).1
  have herr : C * Real.log (T + H) ≤ 2 * C * Real.log T := by
    nlinarith [mul_le_mul_of_nonneg_left hlogUpper hC.le]
  have hcoef : H / (4 * Real.pi) = 4 * (C + 1) := by
    dsimp only [H]
    field_simp
    ring
  have hcount : 0 < (xiZeroCount (T + H) : ℝ) - (xiZeroCount T : ℝ) := by
    rw [hcoef] at hmain
    nlinarith [mul_pos hC hlog0]
  have hcountZ : 0 < xiZeroCount (T + H) - xiZeroCount T := by exact_mod_cast hcount
  have hcard := xiSymmetricMass_diff_eq_card hT0.le (by linarith : T ≤ T + H)
  rw [xiSymmetricMass_eq_two_mul_xiZeroCount hTH0.le,
    xiSymmetricMass_eq_two_mul_xiZeroCount hT0.le] at hcard
  have hcardZ : 0 < ((xiCopiesBand T (T + H)).card : ℤ) := by omega
  exact Finset.card_pos.mp (by exact_mod_cast hcardZ)

/-- The ordinate selected by the two Hausdorff powers at radius one. -/
def primeArchHausdorffSaddleHeight (k r : ℕ) : ℝ :=
  Real.sqrt ((r : ℝ) / ((k + 1 : ℕ) : ℝ))

/-- **Unconditional quadratic-scale source producer.** One fixed-width, nonempty saddle band
retains half its absolute mass for every order and every shift above a common quadratic bound. -/
theorem exists_quadratic_positive_primeArchHausdorff_saddle_bands :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ A : ℕ, 0 < A ∧ ∀ k r : ℕ, A * (k + 1) ^ 2 ≤ r →
      let T := primeArchHausdorffSaddleHeight k r
      (1 / 2 * ∑ q ∈ xiCopiesBand T (T + H), ‖hausdorffAtomTerm 1 k r q‖ ≤
        ∑ q ∈ xiCopiesBand T (T + H), (hausdorffAtomTerm 1 k r q).re) ∧
      0 < ∑ q ∈ xiCopiesBand T (T + H), (hausdorffAtomTerm 1 k r q).re := by
  classical
  obtain ⟨H, hH, S, hS4, hHS, hpop⟩ := exists_fixed_width_xiCopiesBand_nonempty
  let A : ℕ := ⌈S ^ 2 + 32 * H + 1⌉₊
  have hA : S ^ 2 + 32 * H + 1 ≤ (A : ℝ) := Nat.le_ceil _
  have hA0 : 0 < A := by
    have hh : (0 : ℝ) < A := by nlinarith [sq_nonneg S]
    exact_mod_cast hh
  refine ⟨H, hH, A, hA0, fun k r hr => ?_⟩
  let n : ℝ := ((k + 1 : ℕ) : ℝ)
  let T : ℝ := primeArchHausdorffSaddleHeight k r
  have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hn0 : 0 < n := by linarith
  have hr' : (A : ℝ) * n ^ 2 ≤ (r : ℝ) := by
    dsimp only [n]
    exact_mod_cast hr
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hT2 : T ^ 2 = (r : ℝ) / n := Real.sq_sqrt (by positivity)
  have hAn : (A : ℝ) * n ≤ T ^ 2 := by
    rw [hT2, le_div_iff₀ hn0]
    nlinarith
  have hAST : S ^ 2 ≤ T ^ 2 := by
    have hAS : S ^ 2 ≤ (A : ℝ) := by linarith
    have hAA : (A : ℝ) ≤ (A : ℝ) * n := by
      nlinarith [Nat.cast_nonneg (α := ℝ) A]
    exact hAS.trans (hAA.trans hAn)
  have hST : S ≤ T := by nlinarith
  have hT4 : 4 ≤ T := hS4.trans hST
  have hHT : H ≤ T := hHS.trans hST
  have hrT : (r : ℝ) = ((k + 1 : ℕ) : ℝ) * T ^ 2 := by
    change (r : ℝ) = n * T ^ 2
    rw [hT2]
    field_simp
  have hscale : 32 * ((k + 1 : ℕ) : ℝ) * H ≤ T ^ 2 := by
    have hAH : 32 * H ≤ (A : ℝ) := by nlinarith [sq_nonneg S]
    have hh := mul_le_mul_of_nonneg_right hAH hn0.le
    change 32 * n * H ≤ T ^ 2
    nlinarith
  have hretain := half_sum_norm_hausdorffAtomTerm_le_quadratic_band_sum k r hT4 hH hHT hrT hscale
  have hnorm : 0 < ∑ q ∈ xiCopiesBand T (T + H), ‖hausdorffAtomTerm 1 k r q‖ := by
    obtain ⟨q, hq⟩ := hpop T hST
    exact Finset.sum_pos' (fun q _ => norm_nonneg _) ⟨q, hq,
      norm_pos_iff.mpr (hausdorffAtomTerm_one_ne_zero k r q)⟩
  exact ⟨hretain, lt_of_lt_of_le (by linarith :
    0 < 1 / 2 * ∑ q ∈ xiCopiesBand T (T + H), ‖hausdorffAtomTerm 1 k r q‖) hretain⟩

/-- The signed contribution outside the actual saddle band. -/
def primeArchHausdorffSaddleComplement (H : ℝ) (k r : ℕ) : ℝ :=
  ∑' q : {q : XiZeroCopy //
    q ∉ xiCopiesBand (primeArchHausdorffSaddleHeight k r) (primeArchHausdorffSaddleHeight k r + H)},
      (hausdorffAtomTerm 1 k r q.1).re

/-- Exact source identity: the band and its complement recover the prime--archimedean difference. -/
theorem scaledHausdorffMomentDifference_one_eq_saddle_add_complement (H : ℝ) (k r : ℕ) :
    scaledHausdorffMomentDifference 1 normalizedPrimeArchMoment k r =
      (∑ q ∈ xiCopiesBand (primeArchHausdorffSaddleHeight k r)
        (primeArchHausdorffSaddleHeight k r + H), (hausdorffAtomTerm 1 k r q).re) +
      primeArchHausdorffSaddleComplement H k r := by
  have hs : Summable (fun q => hausdorffAtomTerm 1 k r q) :=
    summable_xiCentralScaledHausdorffTerm 1 k r
  have hsre : Summable (fun q => (hausdorffAtomTerm 1 k r q).re) :=
    ⟨_, Complex.hasSum_re hs.hasSum⟩
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum]
  change (∑' q, hausdorffAtomTerm 1 k r q).re = _
  rw [Complex.re_tsum hs]
  exact (hsre.sum_add_tsum_subtype_compl _).symm

/-- Any negative source value in the quadratic region owes a strict deficit outside the band. -/
theorem exists_quadratic_primeArchHausdorff_complement_deficit :
    ∃ H : ℝ, 1 ≤ H ∧ ∃ A : ℕ, 0 < A ∧ ∀ k r : ℕ, A * (k + 1) ^ 2 ≤ r →
      scaledHausdorffMomentDifference 1 normalizedPrimeArchMoment k r < 0 →
      primeArchHausdorffSaddleComplement H k r <
        -(1 / 2 * ∑ q ∈ xiCopiesBand (primeArchHausdorffSaddleHeight k r)
          (primeArchHausdorffSaddleHeight k r + H), ‖hausdorffAtomTerm 1 k r q‖) := by
  obtain ⟨H, hH, A, hA, hbands⟩ := exists_quadratic_positive_primeArchHausdorff_saddle_bands
  refine ⟨H, hH, A, hA, fun k r hr hneg => ?_⟩
  have hretain := (hbands k r hr).1
  have heq := scaledHausdorffMomentDifference_one_eq_saddle_add_complement H k r
  linarith

end

end RHTower
