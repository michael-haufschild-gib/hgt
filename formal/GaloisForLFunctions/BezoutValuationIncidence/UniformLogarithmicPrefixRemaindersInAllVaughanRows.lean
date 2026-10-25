import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicRemaindersInAllVaughanRows

/-!
All five smooth-subtracted Vaughan rows share pointwise logarithmic bounds up
to half damping. Their exact sum determines the both-large remainder, and a
common linear bound controls every finite head.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A bounded sequence has every logarithmic saving relative to a positive prefix power. -/
theorem eventually_bounded_prefix_log_rate {ι : Type*} {f : ι → ℕ → ℝ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hf : ∀ i n, |f i n| ≤ C) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i, |f i n| ≤ C * (n : ℝ) ^ a / Real.log (n : ℝ) ^ q := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_pow_le_sqrt_rpow q ha,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hn hln hn1 i
  have hP : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hn1) ha.le
  have hs : Real.sqrt ((n : ℝ) ^ a) ≤ (n : ℝ) ^ a :=
    Real.sqrt_le_iff.mpr ⟨zero_le_one.trans hP, by
      simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hP (zero_le_one.trans hP)⟩
  exact (hf i n).trans ((le_div_iff₀ (pow_pos (zero_lt_one.trans_le hln) q)).mpr
    (mul_le_mul_of_nonneg_left (hn.trans hs) hC))

/-- The smooth unit-pattern remainder has every logarithmic prefix saving below damping one. -/
theorem eventually_abs_subHalfRemainder_log_rate {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, |subHalfRemainder ε n| ≤
      floorSumRate ((1 - ε : ℝ) : ℂ) * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  let F := floorSumRate ((1 - ε : ℝ) : ℂ)
  have hF : 0 ≤ F := by
    have h := (abs_nonneg (subHalfRemainder ε 1)).trans (abs_subHalfRemainder_le hε hε1 1)
    simpa only [Nat.cast_one, Real.sqrt_one, Real.one_rpow, mul_one] using h
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_log_pow_le_sqrt_rpow q (sub_pos.mpr hε1),
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1] with n hn hln hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have heq : Real.sqrt (n : ℝ) ^ (1 - ε) = Real.sqrt ((n : ℝ) ^ (1 - ε)) := by
    simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0]
    congr 1
    ring
  have hR := abs_subHalfRemainder_le hε hε1 n
  rw [heq] at hR
  apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hln) q)).mpr
  calc
    _ ≤ (F * Real.sqrt ((n : ℝ) ^ (1 - ε))) * Real.sqrt ((n : ℝ) ^ (1 - ε)) :=
      mul_le_mul hR hn (pow_nonneg (zero_le_one.trans hln) q) (by positivity)
    _ = _ := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt (Real.rpow_nonneg hn0 _)]

/-- The pointwise both-large remainder is controlled by the other rows and the actual interior. -/
theorem abs_pmPronicVaughanSmoothRemainder_large_le (ε : ℝ) (U V n : ℕ) :
    |pmPronicVaughanSmoothRemainder ε U V n 3| ≤ |pmBezoutInteriorPrefix ε n| +
      (|pmPronicVaughanSmoothRemainder ε U V n 0| +
        (|pmPronicVaughanSmoothRemainder ε U V n 1| +
          (|pmPronicVaughanSmoothRemainder ε U V n 2| +
            |pmPronicVaughanSmoothRemainder ε U V n 4|))) := by
  let r : Fin 5 → ℝ := fun i => pmPronicVaughanSmoothRemainder ε U V n i
  have heq : r 3 = pmBezoutInteriorPrefix ε n - (r 0 + (r 1 + (r 2 + r 4))) := by
    have h := sum_pmPronicVaughanSmoothRemainder ε U V n
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change r 0 + (r 1 + (r 2 + (r 3 + r 4))) = _ at h
    linarith only [h]
  change |r 3| ≤ _
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add le_rfl
    ((abs_add_le _ _).trans (add_le_add le_rfl
      ((abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))))))

/-- All five actual smooth remainders have common pointwise logarithmic rates, including half damping. -/
theorem exists_uniform_pmPronicVaughanSmoothRemainder_prefix_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ U V : ℕ, ∀ i : Fin 5,
      |pmPronicVaughanSmoothRemainder ε U V n i| ≤
        C * (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q := by
  have hε1 : ε < 1 := by linarith only [hε2]
  let F := floorSumRate ((1 - ε : ℝ) : ℂ)
  have hF : 0 ≤ F := by
    have h := (abs_nonneg (subHalfRemainder ε 1)).trans (abs_subHalfRemainder_le hε hε1 1)
    simpa only [Nat.cast_one, Real.sqrt_one, Real.one_rpow, mul_one] using h
  obtain ⟨A, hA, hsource⟩ := exists_pmPowerDampedCenteredDivisorPrefix_log_rate hε hε2 q
  obtain ⟨B, hB, hsmall⟩ := exists_uniform_patternPrefix_truncatedMoebius_log_rate hε hε2 q
  obtain ⟨D, hD, hfluct⟩ := exists_uniform_pmVaughanConvolutionFluctuation_prefix_log_rate hε hε2 q
  have hunit := eventually_abs_subHalfRemainder_log_rate hε hε1 q
  have hactive := eventually_bounded_prefix_log_rate
    (f := fun _u : Unit => addDiff (pmActiveSawtoothComponent ε))
    (sub_pos.mpr hε1) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (fun _u n => abs_addDiff_pmActiveSawtoothComponent_le_half hε.le n) q
  refine ⟨A + 2 * B + F + D + 1, by positivity, ?_⟩
  filter_upwards [hsource, hsmall, hfluct, hunit, hactive, eventually_ge_atTop 1]
    with n hAn hBn hDn hFn hPn hn U V i
  let S := (n : ℝ) ^ (1 - ε) / Real.log (n : ℝ) ^ q
  have hS : 0 ≤ S := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (pow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) q)
  have h0 : |pmPronicVaughanSmoothRemainder ε U V n 0| ≤ B * S := by
    change |pmPronicVaughanCentredPiece ε U V n 0 -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
        (n : ℝ) ^ (1 - ε)| ≤ _
    simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε, S, mul_div_assoc] using hBn U
  have h1 : |pmPronicVaughanSmoothRemainder ε U V n 1| ≤ B * S := by
    change |pmPronicVaughanCentredPiece ε V U n 0 -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
        (n : ℝ) ^ (1 - ε)| ≤ _
    simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε, S, mul_div_assoc] using hBn V
  have h2 : |pmPronicVaughanSmoothRemainder ε U V n 2| ≤ (F + D) * S := by
    have hcoeff : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
        (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
    rw [pmPronicVaughanSmoothRemainder_smallSmall_eq hε]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_neg]
    have hunit' : |subHalfRemainder ε n| ≤ F * S := by
      simpa only [S, mul_div_assoc] using hFn
    have hfluct' : |pmVaughanConvolutionFluctuationPrefix ε U V n| ≤ D * S := by
      simpa only [pmVaughanConvolutionFluctuationPrefix, S, mul_div_assoc] using hDn U V
    exact (add_le_add ((mul_le_of_le_one_left (abs_nonneg _) hcoeff).trans hunit') hfluct').trans_eq (by ring)
  have h4 : |pmPronicVaughanSmoothRemainder ε U V n 4| ≤ (1 / 2) * S := by
    have heq : pmPronicVaughanSmoothRemainder ε U V n 4 =
        -addDiff (pmActiveSawtoothComponent ε) n := by
      change -(pmPowerDampedDivisorDensity ε).re * n - addDiff (pmActiveSawtoothComponent ε) n -
        (-(pmPowerDampedDivisorDensity ε).re) * n -
          (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
            (n : ℝ) ^ (1 - ε) = _
      ring
    rw [heq, abs_neg]
    simpa only [S, mul_div_assoc] using hPn ()
  have hI : |pmBezoutInteriorPrefix ε n| ≤ (A + 1 / 2) * S := by
    have heq : pmBezoutInteriorPrefix ε n = pmPowerDampedCenteredDivisorPrefix ε n -
        addDiff (pmActiveSawtoothComponent ε) n := by
      rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
      ring
    rw [heq]
    have hA' : |pmPowerDampedCenteredDivisorPrefix ε n| ≤ A * S := by
      simpa only [S, mul_div_assoc] using hAn
    have hP' : |addDiff (pmActiveSawtoothComponent ε) n| ≤ (1 / 2) * S := by
      simpa only [S, mul_div_assoc] using hPn ()
    exact (abs_sub _ _).trans ((add_le_add hA' hP').trans_eq (by ring))
  rw [mul_div_assoc]
  change _ ≤ (A + 2 * B + F + D + 1) * S
  fin_cases i
  · exact h0.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hF, hD]) hS)
  · exact h1.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hF, hD]) hS)
  · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hF, hD]) hS)
  · exact (abs_pmPronicVaughanSmoothRemainder_large_le ε U V n).trans
      ((add_le_add hI (add_le_add h0 (add_le_add h1 (add_le_add h2 h4)))).trans_eq (by ring))
  · exact h4.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hF, hD]) hS)

/-- Unit-bounded coefficients have a common linear centered floor-prefix majorant. -/
theorem abs_patternPrefix_le_linear_of_abs_le_one {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) {r : ℕ → ℝ} (hr : ∀ d, |r d| ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    |patternPrefix ε r n| ≤ (1 + 1 / (1 - ε) + 1 / ε) * n := by
  have hgap : 0 < 1 - ε := sub_pos.mpr hε1
  have hc : DampedClass 1 ε (dampedSignWeight r ε) := by
    intro d
    rw [dampedSignWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_mul_of_nonneg_right (hr d) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have h := abs_weightCenteredPrefix_le_of_dampedClass hε hε1 hc hn
  simp only [one_mul] at h
  have hp : (n : ℝ) ^ (1 - ε) ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by linarith only [hε] : 1 - ε ≤ 1)
  exact h.trans (mul_le_mul_of_nonneg_left hp (by positivity))

/-- One linear majorant pays every finite head of the five actual smooth remainders. -/
theorem exists_uniform_pmPronicVaughanSmoothRemainder_linear_bound
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ U V n : ℕ, 1 ≤ n → ∀ i : Fin 5,
      |pmPronicVaughanSmoothRemainder ε U V n i| ≤ E * n := by
  have hε1 : ε < 1 := by linarith only [hε2]
  let C := 1 + 1 / (1 - ε) + 1 / ε
  have hgap : 0 < 1 - ε := sub_pos.mpr hε1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let K := 2 * ∑' d : ℕ, pmVaughanFloorMajorant ε d / d
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (tsum_nonneg fun d =>
    div_nonneg (pmVaughanFloorMajorant_nonneg ε d) (Nat.cast_nonneg d))
  let c := |subHalfZetaCoeff ε|
  have hc : 0 ≤ c := abs_nonneg _
  have htrunc (U n : ℕ) (hn : 1 ≤ n) : |patternPrefix ε (Sieve.truncatedMoebius U) n| ≤ C * n :=
    abs_patternPrefix_le_linear_of_abs_le_one hε hε1
      (fun d => by simpa only [Real.norm_eq_abs] using Sieve.norm_truncatedMoebius_le_one U d) hn
  refine ⟨4 * C + c + K + 1, by positivity, fun U V n hn i => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h0 : |pmPronicVaughanSmoothRemainder ε U V n 0| ≤ C * n := by
    change |pmPronicVaughanCentredPiece ε U V n 0 -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
        (n : ℝ) ^ (1 - ε)| ≤ _
    simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε] using htrunc U n hn
  have h1 : |pmPronicVaughanSmoothRemainder ε U V n 1| ≤ C * n := by
    change |pmPronicVaughanCentredPiece ε V U n 0 -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
        (n : ℝ) ^ (1 - ε)| ≤ _
    simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
      pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε] using htrunc V n hn
  have hunit : |subHalfRemainder ε n| ≤ (C + c) * n := by
    have hu := abs_patternPrefix_le_linear_of_abs_le_one hε hε1 (r := unitSign)
      (by intro d; simp [unitSign]) hn
    have hp : (n : ℝ) ^ (1 - ε) ≤ n := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [hε] : 1 - ε ≤ 1)
    change |patternPrefix ε unitSign n - subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε)| ≤ _
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0 _)]
    exact (add_le_add hu (mul_le_mul_of_nonneg_left hp hc)).trans_eq (by ring)
  have h2 : |pmPronicVaughanSmoothRemainder ε U V n 2| ≤ (C + c + K) * n := by
    have hcoeff : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
        (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
    rw [pmPronicVaughanSmoothRemainder_smallSmall_eq hε]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_neg]
    exact (add_le_add ((mul_le_of_le_one_left (abs_nonneg _) hcoeff).trans hunit)
      (abs_pmVaughanConvolutionFluctuationPrefix_le_linear hε U V hn)).trans_eq (by ring)
  have h4 : |pmPronicVaughanSmoothRemainder ε U V n 4| ≤ (1 / 2) * n := by
    have hp := (abs_pmPronicVaughanPiece_pole_sub_mean_le hε.le U V n).trans
      (by linarith only [hnR] : (1 / 2 : ℝ) ≤ (1 / 2) * n)
    change |pmPronicVaughanCentredPiece ε U V n 4 -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
        (n : ℝ) ^ (1 - ε)| ≤ _
    simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece] using hp
  have hI : |pmBezoutInteriorPrefix ε n| ≤ (C + 1 / 2) * n := by
    have hM : |pmPowerDampedCenteredDivisorPrefix ε n| ≤ C * n := by
      rw [← patternPrefix_moebius_eq_centeredDivisorPrefix hε]
      exact abs_patternPrefix_le_linear_of_abs_le_one hε hε1 abs_moebiusReal_le_one' hn
    have hP := (abs_addDiff_pmActiveSawtoothComponent_le_half hε.le n).trans
      (by linarith only [hnR] : (1 / 2 : ℝ) ≤ (1 / 2) * n)
    have heq : pmBezoutInteriorPrefix ε n = pmPowerDampedCenteredDivisorPrefix ε n -
        addDiff (pmActiveSawtoothComponent ε) n := by
      rw [pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior]
      ring
    rw [heq]
    exact (abs_sub _ _).trans ((add_le_add hM hP).trans_eq (by ring))
  fin_cases i
  · exact h0.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hc, hK]) hn0)
  · exact h1.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hc, hK]) hn0)
  · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hc, hK]) hn0)
  · exact (abs_pmPronicVaughanSmoothRemainder_large_le ε U V n).trans
      ((add_le_add hI (add_le_add h0 (add_le_add h1 (add_le_add h2 h4)))).trans_eq (by ring))
  · exact h4.trans (mul_le_mul_of_nonneg_right (by linarith only [hC, hc, hK]) hn0)

#print axioms eventually_bounded_prefix_log_rate
#print axioms eventually_abs_subHalfRemainder_log_rate
#print axioms abs_pmPronicVaughanSmoothRemainder_large_le
#print axioms exists_uniform_pmPronicVaughanSmoothRemainder_prefix_log_rate
#print axioms abs_patternPrefix_le_linear_of_abs_le_one
#print axioms exists_uniform_pmPronicVaughanSmoothRemainder_linear_bound
end GaloisForLFunctions.BezoutValuationIncidence
