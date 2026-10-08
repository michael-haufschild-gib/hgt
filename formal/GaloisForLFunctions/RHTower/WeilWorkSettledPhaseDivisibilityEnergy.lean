import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationCosineBound
import GaloisForLFunctions.RHTower.WeilWorkSettledPhasePrimeDifference
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMaskedEnergy

/-!
# Exact density of the divisibility mask in weighted source energy

The mask's square series is q^(-s) times the real zeta series. The zero-index
convention is handled at the L-series level, where its term is zero.
-/

open Complex Filter Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

private theorem divisibility_mask_sq (q n : ℕ) :
    ‖(divisibilityMask q n : ℂ)‖ ^ 2 = divisibilityMask q n := by
  unfold divisibilityMask
  split_ifs <;> norm_num

theorem summable_divisibility_mask_square (q : ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖(divisibilityMask q n : ℂ)‖ ^ 2 / (n : ℝ) ^ s) := by
  refine (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
    (fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun n => ?_
  rw [divisibility_mask_sq]
  unfold divisibilityMask
  split_ifs
  · rfl
  · simp only [zero_div]
    positivity

private theorem real_constant_series {s : ℝ} (hs : 1 < s) :
    (riemannZeta (s : ℂ)).re = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  rw [← LSeries_one_eq_riemannZeta (show 1 < (s : ℂ).re from hs), LSeries,
    Complex.re_tsum (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs))]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, LSeries.term, Real.zero_rpow (by linarith : s ≠ 0)]
  · have he : (n : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm
    simp only [LSeries.term, if_neg hn, Pi.one_apply, he,
      ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]

/-- Exact square mass of the divisibility mask, for every positive modulus. -/
theorem divisibility_mask_square_series {q : ℕ} (hq : q ≠ 0) {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, ‖(divisibilityMask q n : ℂ)‖ ^ 2 / (n : ℝ) ^ s) =
      (q : ℝ) ^ (-s) * ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
  have hm := summable_divisibilityPart q
    (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs))
  have hre : (LSeries (divisibilityPart q 1) (s : ℂ)).re =
      ∑' n : ℕ, ‖(divisibilityMask q n : ℂ)‖ ^ 2 / (n : ℝ) ^ s := by
    rw [LSeries, Complex.re_tsum hm]
    apply tsum_congr
    intro n
    rw [divisibility_mask_sq]
    by_cases hn : n = 0
    · simp [hn, LSeries.term, Real.zero_rpow (by linarith : s ≠ 0)]
    · have he : (n : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm
      simp only [LSeries.term, if_neg hn, divisibilityPart, Pi.one_apply, mul_one,
        he, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [← hre]
  have heq : LSeries (divisibilityPart q 1) (s : ℂ) =
      LSeries (LSeries.convolution (dirichletPoint q) 1) (s : ℂ) := by
    apply LSeries_congr
    intro n hn
    rw [convolution_dirichletPoint hq, if_neg hn]
    by_cases hd : q ∣ n <;> simp [divisibilityPart, divisibilityMask, hd]
  rw [heq, LSeries_convolution' (summable_dirichletPoint q (s : ℂ))
    (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs)), LSeries_dirichletPoint hq,
    LSeries_one_eq_riemannZeta (show 1 < (s : ℂ).re from hs)]
  have hp : (q : ℂ) ^ (-(s : ℂ)) = (((q : ℝ) ^ (-s) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
      (Complex.ofReal_cpow (Nat.cast_nonneg q) (-s)).symm
  rw [hp, Complex.re_ofReal_mul, real_constant_series hs]

/-- The modulus factor is uniform in the entire absolute half-plane. -/
theorem norm_divisibility_LSeries_sq_le_energy {f : ℕ → ℂ} {q : ℕ}
    (hq : q ≠ 0) {s : ℝ} (hs : 1 < s)
    (hf : LSeriesSummable f (s : ℂ))
    (he : Summable (fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s)) :
    ‖LSeries (divisibilityPart q f) (s : ℂ)‖ ^ 2 ≤
      ((∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
        ∑' n : ℕ, 1 / (n : ℝ) ^ s) / q := by
  have hfg : (fun n => f n * (divisibilityMask q n : ℂ)) = divisibilityPart q f := by
    funext n
    exact mul_comm _ _
  have hc := norm_LSeries_mul_sq_le_energy hs
    (by rw [hfg]; exact summable_divisibilityPart q hf) he
    (summable_divisibility_mask_square q hs)
  rw [hfg, divisibility_mask_square_series hq hs] at hc
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hq
  have hp : (q : ℝ) ^ (-s) ≤ (q : ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (show -s ≤ -1 by linarith)
  have hE : 0 ≤ ∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s :=
    tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hZ : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ s :=
    tsum_nonneg fun n => div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ ≤ _ := hc
    _ ≤ (∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
        ((q : ℝ)⁻¹ * ∑' n : ℕ, 1 / (n : ℝ) ^ s) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp hZ) hE
    _ = _ := by ring

end RHTower.WeilSingularArithmetic
