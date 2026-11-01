import GaloisForLFunctions.RHTower.SmoothAFEZetaDualContourLimit
import GaloisForLFunctions.RHTower.SmoothAFETruncation
import GaloisForLFunctions.RHTower.SmoothAFEZetaPoleDecay

/-! # Absolute tails at the square-height Gaussian AFE cutoff

At scale `sqrt(t)`, both exact series are dominated by a constant times
`sqrt(t) n^(-3/2)`. Truncation beyond `t²` therefore has uniformly bounded
error. The shifted pole residue is bounded independently of the height.
-/

noncomputable section
open RHTower Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A common absolute majorant for the actual direct and reflected AFE coefficients. -/
theorem exists_gaussianAFE_term_majorant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ n : ℕ, 1 ≤ n →
      ‖(n : ℂ) ^ (-linePt t) * smoothAFECutoff ((n : ℝ) / Real.sqrt t)‖ ≤
        C * Real.sqrt t * (n : ℝ) ^ (-(3 / 2 : ℝ)) ∧
      ‖(zetaChi (linePt t) * (n : ℂ) ^ (linePt t - 1)) *
        smoothAFEZetaDualWeight t ((n : ℝ) * Real.sqrt t)‖ ≤
        C * Real.sqrt t * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨A, hA, hdir⟩ := exists_norm_smoothAFECutoff_le_neg_rpow (A := 1) zero_lt_one
  obtain ⟨B, hB, hdual⟩ := exists_norm_smoothAFEZetaDualWeight_le_inv
  refine ⟨A + 2 * B, by positivity, fun t ht n hn => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hx : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹ = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]
    norm_num
  have hdir' := hdir (div_pos hn0 hx)
  rw [Real.rpow_neg_one, inv_div] at hdir'
  have hdual' := hdual t (mul_pos hn0 hx)
  rw [abs_of_pos ht0] at hdual'
  have hscale : (1 + t) * ((n : ℝ) * Real.sqrt t)⁻¹ ≤ 2 * Real.sqrt t / (n : ℝ) := by
    have hs := Real.sq_sqrt ht0.le
    have he : (2 * t) * ((n : ℝ) * Real.sqrt t)⁻¹ = 2 * Real.sqrt t / (n : ℝ) := by
      field_simp [hn0.ne', hx.ne']
      nlinarith only [hs]
    rw [← he]
    exact mul_le_mul_of_nonneg_right (by linarith only [ht]) (by positivity)
  have hnormD : ‖(n : ℂ) ^ (-linePt t)‖ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re, linePt_re]
  have hnormR : ‖zetaChi (linePt t) * (n : ℂ) ^ (linePt t - 1)‖ =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [norm_mul, zetaChi_norm_on_line (linePt_re t), one_mul,
      Complex.norm_natCast_cpow_of_pos hn, Complex.sub_re, linePt_re, Complex.one_re]
    norm_num
  have hD : ‖(n : ℂ) ^ (-linePt t) * smoothAFECutoff ((n : ℝ) / Real.sqrt t)‖ ≤
      A * Real.sqrt t * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [norm_mul, hnormD]
    calc _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (A * (Real.sqrt t / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hdir' (by positivity)
      _ = (A * Real.sqrt t) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹) := by ring
      _ = _ := by rw [hp]
  have hR : ‖(zetaChi (linePt t) * (n : ℂ) ^ (linePt t - 1)) *
      smoothAFEZetaDualWeight t ((n : ℝ) * Real.sqrt t)‖ ≤
        (2 * B) * Real.sqrt t * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [norm_mul, hnormR]
    have hb := mul_le_mul_of_nonneg_left hscale hB
    have hb' : ‖smoothAFEZetaDualWeight t ((n : ℝ) * Real.sqrt t)‖ ≤
        B * (2 * Real.sqrt t / (n : ℝ)) := by nlinarith only [hdual', hb]
    calc _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * (B * (2 * Real.sqrt t / (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hb' (by positivity)
      _ = ((2 * B) * Real.sqrt t) * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ)⁻¹) := by ring
      _ = _ := by rw [hp]
  constructor
  · exact hD.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hx.le) (by positivity))
  · exact hR.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hx.le) (by positivity))

private theorem norm_tsum_sub_range_le_of_threeHalves_majorant {f : ℕ → ℂ} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 1 ≤ t)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ C * Real.sqrt t * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
    {L : ℕ} (hL : 1 ≤ L) (hLt : t ^ 2 ≤ (L : ℝ)) :
    ‖(∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n‖ ≤ 2 * C * t ^ (-(1 / 2 : ℝ)) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hmajor : Summable (fun n : ℕ => C * Real.sqrt t * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
    ((summable_nat_add_iff 1).mpr hbase).mul_left _
  have hnorm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hf hmajor
  have hsum : Summable f := hnorm.of_norm
  have hshift : Summable (fun j : ℕ => ((j + L + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (L + 1)).mpr hbase
  have hnormshift : Summable (fun j : ℕ => ‖f (j + L)‖) := (summable_nat_add_iff L).mpr hnorm
  have hsplit := hsum.sum_add_tsum_nat_add L
  have he : (∑' n : ℕ, f n) - ∑ n ∈ Finset.range L, f n = ∑' j : ℕ, f (j + L) := by
    rw [← hsplit, add_sub_cancel_left]
  rw [he]
  have hpower : Real.sqrt t * (L : ℝ) ^ (-(1 / 2 : ℝ)) ≤ t ^ (-(1 / 2 : ℝ)) := by
    have hp := Real.rpow_le_rpow_of_nonpos (pow_pos ht0 2) hLt
      (by norm_num : (-(1 / 2) : ℝ) ≤ 0)
    have he : Real.sqrt t * (t ^ (2 : ℕ)) ^ (-(1 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le,
        ← Real.rpow_add ht0]
      norm_num
    calc _ ≤ Real.sqrt t * (t ^ (2 : ℕ)) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := he
  have htail := RHTower.Sieve.tsum_tail_rpow_neg_le (σ := 3 / 2) (by norm_num) hL
  norm_num only [show (1 - 3 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num,
    show (3 / 2 - 1 : ℝ) = 1 / 2 by norm_num] at htail
  calc _ ≤ ∑' j : ℕ, ‖f (j + L)‖ := norm_tsum_le_tsum_norm hnormshift
    _ ≤ ∑' j : ℕ, C * Real.sqrt t * ((j + L + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
      hnormshift.tsum_le_tsum (fun j => hf (j + L)) (hshift.mul_left _)
    _ = (C * Real.sqrt t) * ∑' j : ℕ, ((j + L + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
    _ ≤ (C * Real.sqrt t) * ((L : ℝ) ^ (-(1 / 2 : ℝ)) / (1 / 2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ 2 * C * t ^ (-(1 / 2 : ℝ)) := by
      nlinarith only [mul_le_mul_of_nonneg_left hpower hC]

/-- Both exact AFE series have uniformly bounded tails after a square-height cutoff. -/
theorem exists_gaussianAFE_truncation_error_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ∀ L : ℕ, 1 ≤ L → t ^ 2 ≤ (L : ℝ) →
      ‖(∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt t) *
          smoothAFECutoff ((n + 1 : ℝ) / Real.sqrt t)) -
        (∑ n ∈ Finset.range L, (n + 1 : ℂ) ^ (-linePt t) *
          smoothAFECutoff ((n + 1 : ℝ) / Real.sqrt t))‖ ≤ C ∧
      ‖(∑' n : ℕ, (zetaChi (linePt t) * (n + 1 : ℂ) ^ (linePt t - 1)) *
          smoothAFEZetaDualWeight t ((n + 1 : ℝ) * Real.sqrt t)) -
        (∑ n ∈ Finset.range L, (zetaChi (linePt t) * (n + 1 : ℂ) ^ (linePt t - 1)) *
          smoothAFEZetaDualWeight t ((n + 1 : ℝ) * Real.sqrt t))‖ ≤ C := by
  obtain ⟨C, hC, hterm⟩ := exists_gaussianAFE_term_majorant
  refine ⟨2 * C, by positivity, fun t ht L hL hLt => ?_⟩
  have hdecay : 2 * C * t ^ (-(1 / 2 : ℝ)) ≤ 2 * C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num : (-(1 / 2) : ℝ) ≤ 0))
      (by positivity : 0 ≤ 2 * C)
  constructor
  · refine (norm_tsum_sub_range_le_of_threeHalves_majorant hC ht ?_ hL hLt).trans hdecay
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using (hterm t ht (n + 1) (by omega)).1
  · refine (norm_tsum_sub_range_le_of_threeHalves_majorant hC ht ?_ hL hLt).trans hdecay
    intro n
    simpa only [Nat.cast_add, Nat.cast_one] using (hterm t ht (n + 1) (by omega)).2

/-- At the square-root smoothing scale, the shifted pole residue is at most one. -/
theorem norm_gaussianAFE_residue_sqrt_le_one {t : ℝ} (ht : 1 ≤ t) :
    ‖smoothAFEZetaShiftedPoleResidue (linePt t) (Real.sqrt t)‖ ≤ 1 := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hx : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hden : t ≤ ‖1 - linePt t‖ := by
    simpa only [abs_of_pos ht0] using norm_one_sub_linePt_ge_abs t
  rw [smoothAFEZetaShiftedPoleResidue, norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, norm_one_sub_linePt_sq_exp]
  have hre : (1 - linePt t).re = 1 / 2 := by rw [Complex.sub_re, Complex.one_re, linePt_re]; norm_num
  rw [hre]
  have hp : (Real.sqrt t) ^ (1 / 2 : ℝ) ≤ t := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0.le]
    norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have he : Real.exp (1 / 4 - t ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [ht])
  rw [div_le_one (ht0.trans_le hden)]
  exact (mul_le_mul hp he (by positivity) ht0.le).trans (by simpa only [mul_one] using hden)

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_gaussianAFE_truncation_error_le
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.norm_gaussianAFE_residue_sqrt_le_one
