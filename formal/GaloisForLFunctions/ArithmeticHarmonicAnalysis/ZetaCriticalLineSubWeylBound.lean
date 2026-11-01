import GaloisForLFunctions.ArithmeticHarmonicAnalysis.SubWeylGaussianAFEBlocks
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.GaussianAFESquareHeightTails
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.SubconvexityDyadicTruncation
import GaloisForLFunctions.RHTower.Sieve.DirichletDyadicTailAssembly

/-! # An unconditional sub-Weyl bound on the critical line

The exact Gaussian approximate functional equation is truncated above `t²`.
Its two finite sums have logarithmically many blocks, each bounded by
`t^(33/200)`. Absolute tails and the pole residue are uniformly bounded.
-/

noncomputable section
open RHTower Complex

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

private theorem gaussianAFE_triangle (x y : ℂ) : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
  calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _

private theorem norm_squareHeight_prefix_le {t C : ℝ} (ht : 8 ≤ t) (hC : 0 ≤ C)
    (f : ℕ → ℂ)
    (hf : ∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ) →
      ‖∑ n ∈ Finset.Ico N (2 * N), f n‖ ≤ C * t ^ (33 / 200 : ℝ)) :
    ‖∑ n ∈ Finset.range (2 ^ zetaDyadicTruncationExponent t - 1), f (n + 1)‖ ≤
      4 * C * t ^ (33 / 200 : ℝ) * Real.log t := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have htrunc := zetaDyadicTruncation_bounds ht
  have hpow : t ^ 2 ≤ t ^ (7 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
  have hblock : ∀ r ∈ Finset.range (zetaDyadicTruncationExponent t),
      ‖∑ n ∈ Finset.Ico (1 * 2 ^ r) (1 * 2 ^ (r + 1)), f n‖ ≤
        C * t ^ (33 / 200 : ℝ) := by
    intro r hr
    have hr' : r + 1 ≤ zetaDyadicTruncationExponent t := Finset.mem_range.mp hr
    have hn : (2 : ℝ) ^ (r + 1) ≤ (2 : ℝ) ^ zetaDyadicTruncationExponent t :=
      pow_le_pow_right₀ (by norm_num) hr'
    have hup : ((2 ^ r : ℕ) : ℝ) ≤ 10 * t ^ (7 / 3 : ℝ) := by
      push_cast
      rw [pow_succ] at hn
      nlinarith only [hn, htrunc.2.1, hpow, sq_nonneg t]
    simpa only [one_mul, pow_succ, Nat.mul_comm] using hf (2 ^ r) Nat.one_le_two_pow hup
  have hs := (RHTower.Sieve.norm_sum_Ico_dyadic_le 1 f
    (zetaDyadicTruncationExponent t)).trans (Finset.sum_le_sum hblock)
  simp only [one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have he : (∑ n ∈ Finset.range (2 ^ zetaDyadicTruncationExponent t - 1), f (n + 1)) =
      ∑ n ∈ Finset.Ico 1 (2 ^ zetaDyadicTruncationExponent t), f n := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_comm]
  rw [he]
  calc _ ≤ (zetaDyadicTruncationExponent t : ℝ) * (C * t ^ (33 / 200 : ℝ)) := hs
    _ ≤ (4 * Real.log t) * (C * t ^ (33 / 200 : ℝ)) :=
      mul_le_mul_of_nonneg_right htrunc.2.2 (by positivity)
    _ = _ := by ring

/-- The actual critical-line zeta function has exponent `33/200 < 1/6`. -/
theorem exists_norm_riemannZeta_half_le_subWeyl :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 8 ≤ t →
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        C * t ^ (33 / 200 : ℝ) * Real.log t := by
  obtain ⟨B, hB, hblocks⟩ := exists_norm_gaussianAFE_blocks_le_subWeyl
  obtain ⟨E, hE, htail⟩ := exists_gaussianAFE_truncation_error_le
  refine ⟨max (8 * B + 2 * E + 1) 16800000, by positivity, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := by linarith only [ht]
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hmu : 1 ≤ t ^ (33 / 200 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hlog : 1 ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) ht
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    have hl := Real.log_two_gt_d9
    linarith only [h, hl]
  by_cases hbig : 1024 * Real.pi ≤ t
  · have hL : 1 ≤ 2 ^ zetaDyadicTruncationExponent t - 1 := by
      have hR : 1 ≤ zetaDyadicTruncationExponent t := by
        unfold zetaDyadicTruncationExponent
        omega
      have hp : 2 ^ (1 : ℕ) ≤ 2 ^ zetaDyadicTruncationExponent t :=
        Nat.pow_le_pow_right (by norm_num) hR
      norm_num at hp
      omega
    have hD := norm_squareHeight_prefix_le ht hB
      (fun n => (n : ℂ) ^ (-linePt t) * smoothAFECutoff ((n : ℝ) / Real.sqrt t))
      (fun N hN hup => (hblocks t hbig N (2 * N) hN (by omega) le_rfl hup).1)
    have hR := norm_squareHeight_prefix_le ht hB
      (fun n => (zetaChi (linePt t) * (n : ℂ) ^ (linePt t - 1)) *
        smoothAFEZetaDualWeight t ((n : ℝ) * Real.sqrt t))
      (fun N hN hup => (hblocks t hbig N (2 * N) hN (by omega) le_rfl hup).2)
    simp only [Nat.cast_add, Nat.cast_one] at hD hR
    obtain ⟨hDt, hRt⟩ := htail t ht1 _ hL (square_le_zetaDyadicTruncation_pred t)
    have hd : ‖∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt t) *
        smoothAFECutoff ((n + 1 : ℝ) / Real.sqrt t)‖ ≤
          4 * B * t ^ (33 / 200 : ℝ) * Real.log t + E := by
      have hn := gaussianAFE_triangle
        (∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt t) * smoothAFECutoff ((n + 1 : ℝ) / Real.sqrt t))
        (∑ n ∈ Finset.range (2 ^ zetaDyadicTruncationExponent t - 1),
          (n + 1 : ℂ) ^ (-linePt t) * smoothAFECutoff ((n + 1 : ℝ) / Real.sqrt t))
      linarith only [hn, hD, hDt]
    have hr : ‖∑' n : ℕ, (zetaChi (linePt t) * (n + 1 : ℂ) ^ (linePt t - 1)) *
        smoothAFEZetaDualWeight t ((n + 1 : ℝ) * Real.sqrt t)‖ ≤
          4 * B * t ^ (33 / 200 : ℝ) * Real.log t + E := by
      have hn := gaussianAFE_triangle
        (∑' n : ℕ, (zetaChi (linePt t) * (n + 1 : ℂ) ^ (linePt t - 1)) *
          smoothAFEZetaDualWeight t ((n + 1 : ℝ) * Real.sqrt t))
        (∑ n ∈ Finset.range (2 ^ zetaDyadicTruncationExponent t - 1),
          (zetaChi (linePt t) * (n + 1 : ℂ) ^ (linePt t - 1)) *
            smoothAFEZetaDualWeight t ((n + 1 : ℝ) * Real.sqrt t))
      linarith only [hn, hR, hRt]
    have hz : ‖riemannZeta (linePt t)‖ ≤ 8 * B * t ^ (33 / 200 : ℝ) * Real.log t + 2 * E + 1 := by
      rw [riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight (Real.sqrt_pos.mpr ht0) t]
      refine (norm_sub_le _ _).trans ?_
      have hn := norm_add_le
        (∑' n : ℕ, (n + 1 : ℂ) ^ (-linePt t) * smoothAFECutoff ((n + 1 : ℝ) / Real.sqrt t))
        (∑' n : ℕ, (zetaChi (linePt t) * (n + 1 : ℂ) ^ (linePt t - 1)) *
          smoothAFEZetaDualWeight t ((n + 1 : ℝ) * Real.sqrt t))
      have he := norm_gaussianAFE_residue_sqrt_le_one ht1
      linarith only [hn, hd, hr, he]
    have hprod : 1 ≤ t ^ (33 / 200 : ℝ) * Real.log t := by
      simpa only [one_mul] using mul_le_mul hmu hlog zero_le_one (by positivity)
    have hconst := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 2 * E + 1 by positivity)
    have hmax := mul_le_mul_of_nonneg_right
      (le_max_left (8 * B + 2 * E + 1) 16800000)
      (show 0 ≤ t ^ (33 / 200 : ℝ) * Real.log t by positivity)
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
    change ‖riemannZeta (linePt t)‖ ≤ _
    nlinarith only [hz, hconst, hmax]
  · have ht4 : t ≤ 4000 := by
      have hp := Real.pi_lt_d2
      linarith only [lt_of_not_ge hbig, hp]
    have hs : t ^ (1 / 6 : ℝ) ≤ t := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (1 / 6 : ℝ) ≤ 1)
    have hbound : t ^ (1 / 6 : ℝ) ≤ 4000 * t ^ (33 / 200 : ℝ) := by
      linarith only [hs, ht4, hmu]
    refine (norm_riemannZeta_half_le_sixth ht).trans ?_
    have hm := mul_le_mul_of_nonneg_right
      (le_max_right (8 * B + 2 * E + 1) 16800000)
      (show 0 ≤ t ^ (33 / 200 : ℝ) * Real.log t by positivity)
    have hb := mul_le_mul_of_nonneg_right hbound (show 0 ≤ 4200 * Real.log t by positivity)
    nlinarith only [hm, hb]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.exists_norm_riemannZeta_half_le_subWeyl
