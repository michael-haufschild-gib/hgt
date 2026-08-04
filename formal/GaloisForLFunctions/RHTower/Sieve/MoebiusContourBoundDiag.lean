import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundSharp
import GaloisForLFunctions.RHTower.Sieve.MellinDecayDiagonal

/-!
# The contour bound at proportional smoothing

The same bound as `MoebiusContourBoundSharp`, at `H = N`.  The point of the specialisation is the
*order of the quantifiers*: the constants now stand outside the quantifier over the cutoff, so the
bound is uniform in `N` and the limit `N → ∞` can be taken.

Nothing in the geometric scaffolding depends on the cutoff — the rectangle, its zero-freeness and
the three bounds on `invZeta` are functions of the contour parameter alone — so only the three decay
constants had to be made uniform.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

/-- **The contour bound, uniform in the cutoff.** -/
theorem exists_norm_tsum_moebius_smoothWeight_le_diag (j : ℕ) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ N : ℝ, 1 ≤ N → ∀ K : ℕ, K₀ ≤ K →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N N (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (invZetaRightBound K * (C * (N + N + 1) ^ rightAbscissa K)) / truncHeight K
            + invZetaEdgeBound K * (C' * (N + N + 1) ^ rightAbscissa K)
                / (truncHeight K) ^ (j + 1) * (rightAbscissa K - leftAbscissa K)
            + invZetaEdgeBound K * (C' * (N + N + 1) ^ rightAbscissa K)
                / (truncHeight K) ^ (j + 1) * (rightAbscissa K - leftAbscissa K)
            + max M₀ (invZetaEdgeBound K)
                * (2 * ((N + N) ^ leftAbscissa K / leftAbscissa K)
                    + 2 * (C * (N + N + 1) ^ leftAbscissa K)) := by
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_diag_upto 1
  obtain ⟨C', hC', hdecj⟩ := exists_bound_mellin_smoothWeight_diag_upto j
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
  refine ⟨C, C', M₀, max K₁ 5, hC, hC', hM₀, fun N hNle K hKle => ?_⟩
  have hN : (0 : ℝ) < N := by linarith
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
  have h16 : (0 : ℝ) < zeroFreeConst / (16 * (Real.log K) ^ 9) := by positivity
  have h2pos : (0 : ℝ) < zeroFreeConst / (2 * (Real.log K) ^ 9) := by positivity
  have h2small : zeroFreeConst / (2 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have h16small : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ 1 / 54 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hA1, hA0]
  have hd1 : 1 < rightAbscissa K := by rw [rightAbscissa]; linarith
  have hc0 : 0 < leftAbscissa K := by rw [leftAbscissa]; linarith
  have hc1 : leftAbscissa K ≤ 1 := by rw [leftAbscissa]; linarith
  have hcd : leftAbscissa K ≤ rightAbscissa K := by rw [leftAbscissa, rightAbscissa]; linarith
  have hT1 : 1 ≤ truncHeight K := by rw [truncHeight]; linarith
  have hT0 : (0 : ℝ) ≤ truncHeight K := by linarith
  have hTK : 3 + 2 * truncHeight K ≤ (K : ℝ) := by rw [truncHeight]; linarith
  have hzf : ∀ s ∈ Set.uIcc (leftAbscissa K) (rightAbscissa K)
      ×ℂ Set.uIcc (-truncHeight K) (truncHeight K), s ≠ 1 → riemannZeta s ≠ 0 := by
    rw [leftAbscissa, rightAbscissa]
    exact zero_free_concrete_rect hlogK hK2
      (fun s h1' h2' h3' h4' => hzfbox s (by linarith [min_le_left δ₁ δ₂]) h2' h3' h4')
      (le_trans hfit (min_le_left _ _)) hT0 hTK
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
  exact norm_tsum_moebius_smoothWeight_le_sharp hN hN j hd1 hc0 hcd hT1
    (invZetaRightBound_nonneg K) (invZetaEdgeBound_nonneg K)
    (le_trans hM₀ (le_max_left _ _)) hzf hFd hFt hFb hFc hFccont
    (hdec1 N hNle (rightAbscissa K))
    (hdecj N hNle (rightAbscissa K))
    (hdec1 N hNle (leftAbscissa K))

end RHTower.Sieve
