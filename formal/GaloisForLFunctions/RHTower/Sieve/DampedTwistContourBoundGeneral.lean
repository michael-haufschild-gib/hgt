import GaloisForLFunctions.RHTower.Sieve.DampedTwistContourBound
import GaloisForLFunctions.RHTower.Sieve.DampedTwistSharpSubstitution
import GaloisForLFunctions.RHTower.Sieve.MoebiusContourBoundGeneral

/-!
# The twisted damped contour bound at an arbitrary smoothing width

The same bound holds for every smoothing width `H`, the cutoff entering only through the explicit
factor `H^{-(j+1)}(N+H+1)^{j+1}` of the uniform decay constant.  Nothing about the twist enters
except through the truncation height `twistHeight K τ` and the side condition `5 + 4|τ| ≤ K`, and
nothing about the damping enters except through the correction factor
`dampedCorrBound P (leftAbscissa K)` multiplying each edge constant.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The twisted damped contour bound at arbitrary smoothing width.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le_general {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) :
    ∃ (C C' M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M₀ ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ N H : ℝ, 0 < N → 0 < H → ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K → 5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((invZetaRightBound K * dampedCorrBound P (leftAbscissa K))
              * (C / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) * (N + H + 1) ^ rightAbscissa K))
            / twistHeight K τ
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ rightAbscissa K)
              / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
              * (C' / H ^ (1 : ℕ) * (N + H + 1) ^ (1 : ℕ) * (N + H + 1) ^ rightAbscissa K)
              / (twistHeight K τ) ^ (0 + 1) * (rightAbscissa K - leftAbscissa K)
          + (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
              * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K)
                  + 2 * (C / H ^ (2 : ℕ) * (N + H + 1) ^ (2 : ℕ) * (N + H + 1) ^ leftAbscissa K)) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, hC, hdec1⟩ := exists_bound_mellin_smoothWeight_uniform_upto 1
  obtain ⟨C', hC', hdecj⟩ := exists_bound_mellin_smoothWeight_uniform_upto 0
  obtain ⟨δ₁, hδ₁, hzfbox⟩ := exists_zero_free_box 1
  obtain ⟨δ₂, hδ₂, M₀, hM₀, hbdbox⟩ := exists_bound_invZeta_low_box 2 (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (Real.log n) ^ (9 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ Real.log n := hlog.eventually_ge_atTop 3
  have h2 : ∀ᶠ n : ℕ in atTop,
      zeroFreeConst / (16 * min δ₁ δ₂) ≤ (Real.log n) ^ (9 : ℕ) := hpow.eventually_ge_atTop _
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨C, C', M₀, max K₁ 5, hC, hC', hM₀, fun t ht0 ht1 N H hN hH τ K hKle hKτ => ?_⟩
  obtain ⟨hlogK, hfitpow⟩ := hK₁ K (le_trans (le_max_left _ _) hKle)
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hK2 : 2 ≤ K := by omega
  have hδ0 : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hL9 := twentySeven_le_log_pow hlogK
  have hfit : zeroFreeConst / (16 * (Real.log K) ^ (9 : ℕ)) ≤ min δ₁ δ₂ := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hfitpow
    linarith
  have hT1 : 1 ≤ twistHeight K τ := one_le_twistHeight hKτ
  have hchalf : 1 / 2 ≤ leftAbscissa K := half_le_leftAbscissa hlogK
  have hcd : leftAbscissa K ≤ rightAbscissa K := leftAbscissa_le_rightAbscissa hlogK
  have hcorr0 : 0 ≤ dampedCorrBound P (leftAbscissa K) := dampedCorrBound_nonneg hP2 hchalf
  have hzf := zero_free_twist_rect (τ := τ) hlogK hK2
    (fun s h1' h2' h3' h4' => hzfbox s (by linarith [min_le_left δ₁ δ₂]) h2' h3' h4')
    (le_trans hfit (min_le_left _ _)) hKτ
  have hFd : ∀ y : ℝ,
      ‖dampedInvZeta P t ((rightAbscissa K : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ invZetaRightBound K * dampedCorrBound P (leftAbscissa K) := by
    intro y
    refine norm_dampedInvZeta_shift_le hP2 ht0 ht1 hchalf
      (s := (rightAbscissa K : ℂ) + (y : ℝ) * Complex.I) (by simp [hcd]) τ
      (invZetaRightBound_nonneg K) ?_
    exact norm_invZetaTwist_right_le hlogK τ y
  have hFt : ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖dampedInvZeta P t ((x : ℂ) + ((twistHeight K τ : ℝ) : ℂ) * Complex.I
          + (τ : ℂ) * Complex.I)‖
        ≤ invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K) := by
    intro x hx
    refine norm_dampedInvZeta_shift_le hP2 ht0 ht1 hchalf
      (s := (x : ℂ) + ((twistHeight K τ : ℝ) : ℂ) * Complex.I) (by simp [hx.1.le]) τ
      (invZetaEdgeBound_nonneg K) ?_
    exact norm_invZetaTwist_top_le hlogK hK2 hKτ x hx
  have hFb : ∀ x ∈ Set.Ioc (leftAbscissa K) (rightAbscissa K),
      ‖dampedInvZeta P t ((x : ℂ) + ((-twistHeight K τ : ℝ) : ℂ) * Complex.I
          + (τ : ℂ) * Complex.I)‖
        ≤ invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K) := by
    intro x hx
    refine norm_dampedInvZeta_shift_le hP2 ht0 ht1 hchalf
      (s := (x : ℂ) + ((-twistHeight K τ : ℝ) : ℂ) * Complex.I) (by simp [hx.1.le]) τ
      (invZetaEdgeBound_nonneg K) ?_
    exact norm_invZetaTwist_bot_le hlogK hK2 hKτ x hx
  have hFc : ∀ y ∈ Set.Icc (-twistHeight K τ) (twistHeight K τ),
      ‖dampedInvZeta P t ((leftAbscissa K : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖
        ≤ max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K) := by
    intro y hy
    refine norm_dampedInvZeta_shift_le hP2 ht0 ht1 hchalf
      (s := (leftAbscissa K : ℂ) + (y : ℝ) * Complex.I) (by simp) τ
      (le_trans hM₀ (le_max_left _ _)) ?_
    exact norm_invZetaTwist_left_le hlogK hK2
      (fun s h1' h2' h3' => hbdbox s (by linarith [min_le_right δ₁ δ₂]) h2' h3') hfit y hy
  have hFccont := continuousOn_dampedInvZetaTwist_left_line hP2 t τ
    (by linarith : (0 : ℝ) ≤ twistHeight K τ)
    (leftAbscissa_pos hlogK) (leftAbscissa_le_one hlogK)
    (le_of_lt (one_lt_rightAbscissa hlogK)) hzf
  exact norm_tsum_dampedTwist_smoothWeight_le_sharp hPprime ht0 ht1 hN hH 0 τ
    (one_lt_rightAbscissa hlogK) (leftAbscissa_pos hlogK) hcd hT1
    (mul_nonneg (invZetaRightBound_nonneg K) hcorr0)
    (mul_nonneg (invZetaEdgeBound_nonneg K) hcorr0)
    (mul_nonneg (le_trans hM₀ (le_max_left _ _)) hcorr0) hzf hFd hFt hFb hFc hFccont
    (hdec1 N H hN hH (rightAbscissa K))
    (hdecj N H hN hH (rightAbscissa K))
    (hdec1 N H hN hH (leftAbscissa K))

end

end RHTower.Sieve
