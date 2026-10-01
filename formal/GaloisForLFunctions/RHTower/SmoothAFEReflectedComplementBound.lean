import GaloisForLFunctions.RHTower.SmoothAFEReflectedComplementScale
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiPowerBound

open Complex
noncomputable section
namespace RHTower

/-- At conductor-sized smoothing, every original complementary coefficient obeys a
uniform summable envelope. The constant is independent of smoothing and height. -/
theorem exists_norm_reflectedComplementCoefficient_le_conductor
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 1 ≤ N → ∀ tau : ℝ, N ≤ tau → tau ≤ 2 * N →
      ∀ n : ℕ, ‖smoothAFEZetaRightComplementCoefficient d tau N n‖ ≤
        C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨D, hD, hdeep⟩ :=
    exists_norm_smoothAFEZetaDisplacedDeepCoefficient_uniform_scale_le hd hdhalf
  obtain ⟨K, hK, hchi⟩ := exists_norm_zetaChi_fixed_right_line_le_rpow hd hdhalf
  refine ⟨81 * K * D, by positivity, ?_⟩
  intro N hN tau hNt htN n
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have htpos : 0 < tau := hNpos.trans_le hNt
  have hmax : max 1 |tau| = tau := by
    rw [abs_of_pos htpos, max_eq_right (hN.trans hNt)]
  have hchiN : ‖zetaChi (rightDisplacedLinePt d tau)‖ ≤ K / N ^ d := by
    have h := hchi tau
    rw [hmax] at h
    exact h.trans (div_le_div_of_nonneg_left hK
      (Real.rpow_pos_of_pos hNpos _) (Real.rpow_le_rpow hNpos.le hNt hd.le))
  have hheight : (1 + |(-tau)|) ^ 4 ≤ (3 * N) ^ 4 := by
    rw [abs_neg, abs_of_pos htpos]
    exact pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hdeepN : ‖smoothAFEZetaDisplacedDeepCoefficient d (-tau) N n‖ ≤
      D * N ^ (d - 4) * (3 * N) ^ 4 * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) :=
    (hdeep N hNpos (-tau) n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight (by positivity)) (by positivity))
  have hscale : N ^ (d - 4) * N ^ (4 : ℕ) = N ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    norm_num
  rw [smoothAFEZetaRightComplementCoefficient_eq_neg_chi_mul_deep hd hdhalf hNpos,
    norm_mul, norm_neg]
  calc
    _ ≤ (K / N ^ d) *
        (D * N ^ (d - 4) * (3 * N) ^ 4 * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) :=
      mul_le_mul hchiN hdeepN (norm_nonneg _) (by positivity)
    _ = (81 * K * D * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) *
        (N ^ (d - 4) * N ^ (4 : ℕ) / N ^ d) := by ring
    _ = _ := by rw [hscale, div_self (Real.rpow_pos_of_pos hNpos d).ne', mul_one]

end RHTower
