import GaloisForLFunctions.RHTower.ReflectedCompactDeepUniformScale
import GaloisForLFunctions.RHTower.CompactGaussianReflectedRowBounds

open Complex
noncomputable section
namespace RHTower

/-- The original complementary coefficients have one summable envelope uniform
in displacement and the wider conductor height band needed by compact discs. -/
theorem exists_norm_reflectedComplementCoefficient_le_conductor_band {d₀ : ℝ}
    (hd₀0 : 0 ≤ d₀) (hd₀half : d₀ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ → ∀ N : ℝ, 1 ≤ N →
      ∀ tau : ℝ, N / 2 ≤ max 1 |tau| → max 1 |tau| ≤ 3 * N → ∀ n : ℕ,
        ‖smoothAFEZetaRightComplementCoefficient d tau N n‖ ≤
          C * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
  obtain ⟨D, hD, hdeep⟩ := exists_norm_smoothAFEZetaDisplacedDeepCoefficient_uniform_strip_scale_le
  obtain ⟨K, hK, hrow⟩ := exists_reflectedCompactGaussianRow_band_bounds hd₀0 hd₀half
  refine ⟨256 * D * K, by positivity, ?_⟩
  intro d hd hdd₀ N hN tau hlow hupp n
  have hdhalf : d < 1 / 2 := hdd₀.trans_lt hd₀half
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hchi : ‖zetaChi (rightDisplacedLinePt d tau)‖ * N ^ d ≤ K := by
    have h := (hrow ((1 / 2 + d : ℝ) : ℂ)
      (by simp; linarith) (by simpa using hdd₀) N hNpos tau
      (by simpa using hlow) (by simpa using hupp)).1
    rw [norm_reflectedCompactGaussianRow _ hNpos] at h
    simpa [rightDisplacedLinePt] using h
  have hheight : (1 + |(-tau)|) ^ 4 ≤ (4 * N) ^ 4 := by
    rw [abs_neg]
    apply pow_le_pow_left₀ (by positivity)
    have ht : |tau| ≤ 3 * N := (le_max_right _ _).trans hupp
    linarith
  have hdeepN : ‖smoothAFEZetaDisplacedDeepCoefficient d (-tau) N n‖ ≤
      D * N ^ (d - 4) * (4 * N) ^ 4 * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) :=
    (hdeep d hd hdhalf N hNpos (-tau) n).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight (by positivity)) (by positivity))
  have hscale : N ^ (d - 4) * N ^ (4 : ℕ) = N ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1
    norm_num
  rw [smoothAFEZetaRightComplementCoefficient_eq_neg_chi_mul_deep hd hdhalf hNpos,
    norm_mul, norm_neg]
  calc
    _ ≤ ‖zetaChi (rightDisplacedLinePt d tau)‖ *
        (D * N ^ (d - 4) * (4 * N) ^ 4 * (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hdeepN (norm_nonneg _)
    _ = 256 * D * (‖zetaChi (rightDisplacedLinePt d tau)‖ * N ^ d) *
        (1 / (n + 1 : ℝ) ^ (9 / 2 : ℝ)) := by
      rw [mul_pow, ← hscale]
      ring
    _ ≤ _ := by gcongr

end RHTower

