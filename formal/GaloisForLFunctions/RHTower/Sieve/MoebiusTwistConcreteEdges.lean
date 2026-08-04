import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistEdgeSubstitution
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBound

/-!
# The concrete rectangle for a twisted contour

The twist by `τ` moves every height by `τ`, so the truncation height available to it is

    twistHeight K τ = truncHeight K - |τ|,

chosen so that `|τ| + twistHeight K τ = truncHeight K` exactly: the twisted contour occupies the same
band as the untwisted one, and the zero-free rectangle is the one already proved.

Collected here are the geometry of the two abscissae, the zero-freeness of the band, and the three
edge bounds at the shifted heights.  Each edge estimate of the untwisted argument is pointwise in the
height, so it applies at `y + τ` directly; the side condition `5 + 4|τ| ≤ K` is what keeps the two
horizontal edges at distance at least one from the real axis.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- The truncation height available to the twist. -/
noncomputable def twistHeight (K : ℕ) (τ : ℝ) : ℝ := truncHeight K - |τ|

/-- The twisted contour occupies the same band as the untwisted one. -/
theorem abs_add_twistHeight (K : ℕ) (τ : ℝ) : |τ| + twistHeight K τ = truncHeight K := by
  rw [twistHeight]; ring

section Geometry

variable {K : ℕ}

theorem twentySeven_le_log_pow (hlogK : (3 : ℝ) ≤ Real.log K) : (27 : ℝ) ≤ (Real.log K) ^ 9 := by
  calc (27 : ℝ) = 3 ^ 3 := by norm_num
    _ ≤ (Real.log K) ^ 3 := by gcongr
    _ ≤ (Real.log K) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)

theorem rightAbscissa_gap_small (hlogK : (3 : ℝ) ≤ Real.log K) :
    zeroFreeConst / (2 * (Real.log K) ^ 9) ≤ 1 / 54 := by
  have hL9 := twentySeven_le_log_pow hlogK
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hL9, zeroFreeConst_le_one, zeroFreeConst_pos]

theorem leftAbscissa_gap_small (hlogK : (3 : ℝ) ≤ Real.log K) :
    zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 54 := by
  have hL9 := twentySeven_le_log_pow hlogK
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hL9, zeroFreeConst_le_one, zeroFreeConst_pos]

theorem rightAbscissa_gap_pos (hlogK : (3 : ℝ) ≤ Real.log K) :
    0 < zeroFreeConst / (2 * (Real.log K) ^ 9) := by
  have : (27 : ℝ) ≤ (Real.log K) ^ 9 := twentySeven_le_log_pow hlogK
  have := zeroFreeConst_pos
  positivity

theorem leftAbscissa_gap_pos (hlogK : (3 : ℝ) ≤ Real.log K) :
    0 < zeroFreeConst / (16 * (Real.log K) ^ 9) := by
  have : (27 : ℝ) ≤ (Real.log K) ^ 9 := twentySeven_le_log_pow hlogK
  have := zeroFreeConst_pos
  positivity

theorem one_lt_rightAbscissa (hlogK : (3 : ℝ) ≤ Real.log K) : 1 < rightAbscissa K := by
  rw [rightAbscissa]; linarith [rightAbscissa_gap_pos hlogK]

theorem rightAbscissa_le_two (hlogK : (3 : ℝ) ≤ Real.log K) : rightAbscissa K ≤ 2 := by
  rw [rightAbscissa]; linarith [rightAbscissa_gap_small hlogK]

theorem leftAbscissa_pos (hlogK : (3 : ℝ) ≤ Real.log K) : 0 < leftAbscissa K := by
  rw [leftAbscissa]; linarith [leftAbscissa_gap_small hlogK]

theorem leftAbscissa_le_one (hlogK : (3 : ℝ) ≤ Real.log K) : leftAbscissa K ≤ 1 := by
  rw [leftAbscissa]; linarith [leftAbscissa_gap_pos hlogK]

theorem leftAbscissa_le_rightAbscissa (hlogK : (3 : ℝ) ≤ Real.log K) :
    leftAbscissa K ≤ rightAbscissa K := by
  rw [leftAbscissa, rightAbscissa]
  linarith [leftAbscissa_gap_pos hlogK, rightAbscissa_gap_pos hlogK]

theorem truncHeight_nonneg (hK : (3 : ℝ) ≤ (K : ℝ)) : 0 ≤ truncHeight K := by
  rw [truncHeight]; linarith

theorem three_add_two_mul_truncHeight_le (K : ℕ) : 3 + 2 * truncHeight K ≤ (K : ℝ) := by
  rw [truncHeight]; linarith

theorem one_add_abs_le_twistHeight {τ : ℝ} (hKτ : 5 + 4 * |τ| ≤ (K : ℝ)) :
    1 + |τ| ≤ twistHeight K τ := by
  rw [twistHeight, truncHeight]
  linarith

theorem one_le_twistHeight {τ : ℝ} (hKτ : 5 + 4 * |τ| ≤ (K : ℝ)) : 1 ≤ twistHeight K τ := by
  linarith [one_add_abs_le_twistHeight hKτ, abs_nonneg τ]

end Geometry

/-- **The band of the twisted contour is zero-free.** -/
theorem zero_free_twist_rect {K : ℕ} {τ δ₀ : ℝ} (hlogK : (3 : ℝ) ≤ Real.log K) (hK2 : 2 ≤ K)
    (hzfbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → s ≠ 1 → riemannZeta s ≠ 0)
    (hfit : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ δ₀)
    (hKτ : 5 + 4 * |τ| ≤ (K : ℝ)) :
    ∀ s ∈ Set.uIcc (leftAbscissa K) (rightAbscissa K)
      ×ℂ Set.uIcc (-(|τ| + twistHeight K τ)) (|τ| + twistHeight K τ),
      s ≠ 1 → riemannZeta s ≠ 0 := by
  have hK3 : (3 : ℝ) ≤ (K : ℝ) := by linarith [abs_nonneg τ]
  rw [abs_add_twistHeight, leftAbscissa, rightAbscissa]
  exact zero_free_concrete_rect hlogK hK2 hzfbox hfit (truncHeight_nonneg hK3)
    (three_add_two_mul_truncHeight_le K)

/-- **The right edge of the twisted contour.** -/
theorem norm_invZetaTwist_right_le {K : ℕ} (hlogK : (3 : ℝ) ≤ Real.log K) (τ y : ℝ) :
    ‖invZeta ((rightAbscissa K : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖
      ≤ invZetaRightBound K := by
  have hrw : ((rightAbscissa K : ℝ) : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I
      = ((rightAbscissa K : ℝ) : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hrw]
  have h := norm_invZeta_right_le (d := rightAbscissa K) (y := y + τ) (one_lt_rightAbscissa hlogK)
  rw [invZetaRightBound, rightAbscissa]
  rw [rightAbscissa] at h
  simpa using h

/-- The horizontal edges of the twisted contour, at any admissible height. -/
theorem norm_invZetaTwist_horizontal_le {K : ℕ} (hlogK : (3 : ℝ) ≤ Real.log K) (hK2 : 2 ≤ K)
    {t : ℝ} (ht : 1 ≤ |t|) (htK : 3 + 2 * |t| ≤ (K : ℝ)) :
    ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖invZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ invZetaEdgeBound K := by
  intro x hx
  rw [leftAbscissa] at hx
  rw [rightAbscissa] at hx
  rw [invZetaEdgeBound]
  exact norm_invZeta_horizontal_le hlogK hK2 ht htK hx.1.le hx.2

/-- **The top edge of the twisted contour.** -/
theorem norm_invZetaTwist_top_le {K : ℕ} {τ : ℝ} (hlogK : (3 : ℝ) ≤ Real.log K) (hK2 : 2 ≤ K)
    (hKτ : 5 + 4 * |τ| ≤ (K : ℝ)) :
    ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖invZeta ((x : ℂ) + ((twistHeight K τ : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ invZetaEdgeBound K := by
  intro x hx
  have hrw : ((x : ℝ) : ℂ) + ((twistHeight K τ : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I
      = ((x : ℝ) : ℂ) + ((twistHeight K τ + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hrw]
  have hband := abs_add_twistHeight K τ
  have hTK := three_add_two_mul_truncHeight_le K
  have h1τ := one_add_abs_le_twistHeight hKτ
  have hpos : (0 : ℝ) < twistHeight K τ + τ := by linarith [neg_abs_le τ]
  refine norm_invZetaTwist_horizontal_le hlogK hK2 ?_ ?_ x hx
  · rw [abs_of_pos hpos]; linarith [neg_abs_le τ]
  · rw [abs_of_pos hpos]; linarith [le_abs_self τ]

/-- **The bottom edge of the twisted contour.** -/
theorem norm_invZetaTwist_bot_le {K : ℕ} {τ : ℝ} (hlogK : (3 : ℝ) ≤ Real.log K) (hK2 : 2 ≤ K)
    (hKτ : 5 + 4 * |τ| ≤ (K : ℝ)) :
    ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖invZeta ((x : ℂ) + ((-twistHeight K τ : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ invZetaEdgeBound K := by
  intro x hx
  have hrw : ((x : ℝ) : ℂ) + ((-twistHeight K τ : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I
      = ((x : ℝ) : ℂ) + ((-twistHeight K τ + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hrw]
  have hband := abs_add_twistHeight K τ
  have hTK := three_add_two_mul_truncHeight_le K
  have h1τ := one_add_abs_le_twistHeight hKτ
  have hneg : -twistHeight K τ + τ < 0 := by linarith [le_abs_self τ]
  refine norm_invZetaTwist_horizontal_le hlogK hK2 ?_ ?_ x hx
  · rw [abs_of_neg hneg]; linarith [le_abs_self τ]
  · rw [abs_of_neg hneg]; linarith [neg_abs_le τ]

/-- **The left edge of the twisted contour.** -/
theorem norm_invZetaTwist_left_le {K : ℕ} {τ δ₀ M₀ : ℝ} (hlogK : (3 : ℝ) ≤ Real.log K)
    (hK2 : 2 ≤ K)
    (hbdbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 1 → ‖invZeta s‖ ≤ M₀)
    (hfit : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ δ₀) :
    ∀ y ∈ Set.Icc (-twistHeight K τ) (twistHeight K τ),
      ‖invZeta ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ max M₀ (invZetaEdgeBound K) := by
  intro y hy
  have hrw : ((leftAbscissa K : ℝ) : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I
      = ((leftAbscissa K : ℝ) : ℂ) + ((y + τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hrw]
  have hband := abs_add_twistHeight K τ
  have hTK := three_add_two_mul_truncHeight_le K
  have hyabs : |y + τ| ≤ truncHeight K := by
    rw [abs_le]
    exact ⟨by linarith [hy.1, neg_abs_le τ], by linarith [hy.2, le_abs_self τ]⟩
  have h := norm_invZeta_left_line_le (N := K) (M₀ := M₀) (δ₀ := δ₀) hlogK hK2 hbdbox hfit
    (y := y + τ) (by linarith)
  rw [leftAbscissa, invZetaEdgeBound]
  exact h

end RHTower.Sieve
