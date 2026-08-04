import GaloisForLFunctions.RHTower.Sieve.PerronEdgeSubstitution
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeConcreteRect

/-!
# The contour bound at the concrete rectangle

Substituting the concrete geometry into the four-edge inequality gives an unconditional bound for
the smoothed Möbius sum in which every quantity is an explicit function of the arithmetic parameter
`K`: the two abscissae and the truncation height are

    c(K) = 1 - c₀/(16 log⁹K),   d(K) = 1 + c₀/(2 log⁹K),   T(K) = (K-3)/2,

and the three edge bounds are the estimates proved for exactly these lines.  Note that `T(K)` is
chosen so that `3 + 2T(K) = K` exactly, which is the largest height the quantitative zero-free
region supports at parameter `K`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- The left abscissa of the contour. -/
noncomputable def leftAbscissa (K : ℕ) : ℝ := 1 - zeroFreeConst / (16 * (Real.log K) ^ 9)

/-- The right abscissa of the contour. -/
noncomputable def rightAbscissa (K : ℕ) : ℝ := 1 + zeroFreeConst / (2 * (Real.log K) ^ 9)

/-- The truncation height. -/
noncomputable def truncHeight (K : ℕ) : ℝ := ((K : ℝ) - 3) / 2

/-- The bound for `invZeta` on the left and horizontal edges. -/
noncomputable def invZetaEdgeBound (K : ℕ) : ℝ :=
  2 / Real.exp ((-22 - 3 * Real.log (1 + 1 / (zeroFreeConst / (2 * (Real.log K) ^ 9)))
      - Real.log (5 / 2 + Real.log K)) / 4)

/-- The bound for `invZeta` on the right edge. -/
noncomputable def invZetaRightBound (K : ℕ) : ℝ :=
  Real.exp (22 / 4) * (1 + 1 / (zeroFreeConst / (2 * (Real.log K) ^ 9)))

theorem invZetaEdgeBound_nonneg (K : ℕ) : 0 ≤ invZetaEdgeBound K := by
  rw [invZetaEdgeBound]
  positivity

theorem invZetaRightBound_nonneg (K : ℕ) : 0 ≤ invZetaRightBound K := by
  rw [invZetaRightBound]
  have hA0 := zeroFreeConst_pos
  positivity

/-- **The contour bound.**  Unconditional: for all large `K` the smoothed Möbius sum is bounded by
the three edge contributions at the concrete rectangle. -/
theorem exists_norm_tsum_moebius_smoothWeight_le_concrete {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    (j : ℕ) :
    ∃ (C M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K * C) / truncHeight K
            + invZetaEdgeBound K * C / (truncHeight K) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * C / (truncHeight K) ^ (j + 1)
                * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) + 2 * C) := by
  obtain ⟨C, hC, hmain⟩ := exists_norm_tsum_moebius_smoothWeight_le hN hH j 2
  obtain ⟨δ₁, hδ₁, hzfbox⟩ := exists_zero_free_box 1
  obtain ⟨δ₂, hδ₂, M₀, hM₀, hbdbox⟩ := exists_bound_invZeta_low_box 2 (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log n) ^ 9) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 3
  have h2 : ∀ᶠ n : ℕ in atTop,
      zeroFreeConst / (16 * min δ₁ δ₂) ≤ (Real.log n) ^ 9 := hpow.eventually_ge_atTop _
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨C, M₀, max K₁ 5, hC, hM₀, fun K hKle => ?_⟩
  obtain ⟨hlogK, hfitpow⟩ := hK₁ K (le_trans (le_max_left _ _) hKle)
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hK2 : 2 ≤ K := by omega
  have hKR : (5 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK5
  have hA0 := zeroFreeConst_pos
  have hA1 := zeroFreeConst_le_one
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hL9 : (27 : ℝ) ≤ (Real.log K) ^ 9 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (Real.log K) ^ 3 := by gcongr
      _ ≤ (Real.log K) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL9pos : (0 : ℝ) < (Real.log K) ^ 9 := by linarith
  have hδ0 : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hfit : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ min δ₁ δ₂ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hfitpow
    linarith
  -- the geometry
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log K) ^ 9) := by positivity
  have h2pos : (0 : ℝ) < zeroFreeConst / (2 * (Real.log K) ^ 9) := by positivity
  have h2small : zeroFreeConst / (2 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have h16small : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hd1 : 1 < rightAbscissa K := by rw [rightAbscissa]; linarith
  have hd2 : rightAbscissa K ≤ 2 := by rw [rightAbscissa]; linarith
  have hc0 : 0 < leftAbscissa K := by rw [leftAbscissa]; linarith
  have hc1 : leftAbscissa K ≤ 1 := by rw [leftAbscissa]; linarith
  have hcd : leftAbscissa K ≤ rightAbscissa K := by rw [leftAbscissa, rightAbscissa]; linarith
  have hT1 : 1 ≤ truncHeight K := by rw [truncHeight]; linarith
  have hT0 : (0 : ℝ) ≤ truncHeight K := by linarith
  have hTK : 3 + 2 * truncHeight K ≤ (K : ℝ) := by rw [truncHeight]; linarith
  -- zero-freeness of the rectangle
  have hzf : ∀ s ∈ Set.uIcc (leftAbscissa K) (rightAbscissa K)
      ×ℂ Set.uIcc (-truncHeight K) (truncHeight K), s ≠ 1 → riemannZeta s ≠ 0 := by
    rw [leftAbscissa, rightAbscissa]
    exact zero_free_concrete_rect hlogK hK2
      (fun s h1' h2' h3' h4' => hzfbox s (by linarith [min_le_left δ₁ δ₂]) h2' h3' h4')
      (le_trans hfit (min_le_left _ _)) hT0 hTK
  -- the edge bounds
  have hFd : ∀ y : ℝ, ‖invZeta ((rightAbscissa K : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ invZetaRightBound K := by
    intro y
    have h := norm_invZeta_right_le (d := rightAbscissa K) (y := y) hd1
    rw [invZetaRightBound, rightAbscissa]
    rw [rightAbscissa] at h
    simpa using h
  have hhor : ∀ (t : ℝ), 1 ≤ |t| → 3 + 2 * |t| ≤ (K : ℝ) →
      ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
        ‖invZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ invZetaEdgeBound K := by
    intro t ht htK x hx
    rw [leftAbscissa] at hx
    rw [rightAbscissa] at hx
    rw [invZetaEdgeBound]
    exact norm_invZeta_horizontal_le hlogK hK2 ht htK hx.1.le hx.2
  have hFt : ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖invZeta ((x : ℂ) + ((truncHeight K : ℝ) : ℂ) * Complex.I)‖ ≤ invZetaEdgeBound K :=
    hhor (truncHeight K) (by rw [abs_of_pos (by linarith)]; exact hT1)
      (by rw [abs_of_pos (by linarith)]; exact hTK)
  have hFb : ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖invZeta ((x : ℂ) + ((-truncHeight K : ℝ) : ℂ) * Complex.I)‖ ≤ invZetaEdgeBound K :=
    hhor (-truncHeight K) (by rw [abs_neg, abs_of_pos (by linarith)]; exact hT1)
      (by rw [abs_neg, abs_of_pos (by linarith)]; exact hTK)
  have hFc : ∀ y ∈ Set.Icc (-truncHeight K) (truncHeight K),
      ‖invZeta ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ max M₀ (invZetaEdgeBound K) := by
    intro y hy
    have hyabs : |y| ≤ truncHeight K := abs_le.2 ⟨hy.1, hy.2⟩
    have h := norm_invZeta_left_line_le (N := K) (M₀ := M₀) (δ₀ := min δ₁ δ₂) hlogK hK2
      (fun s h1' h2' h3' => hbdbox s (by linarith [min_le_right δ₁ δ₂]) h2' h3')
      hfit (y := y) (by linarith)
    rw [leftAbscissa, invZetaEdgeBound]
    exact h
  have hFccont : ContinuousOn
      (fun y : ℝ => invZeta ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-truncHeight K) (truncHeight K)) :=
    continuousOn_invZeta_left_line hc1 (by linarith) hzf
  exact hmain (leftAbscissa K) (rightAbscissa K) (truncHeight K) (invZetaRightBound K)
    (invZetaEdgeBound K) (max M₀ (invZetaEdgeBound K)) hd1 hd2 hc0 hcd hT1
    (invZetaRightBound_nonneg K) (invZetaEdgeBound_nonneg K)
    (le_trans hM₀ (le_max_left _ _)) hzf hFd hFt hFb hFc hFccont

end RHTower.Sieve
