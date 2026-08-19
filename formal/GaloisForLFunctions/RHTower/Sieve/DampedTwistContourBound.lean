import GaloisForLFunctions.RHTower.Sieve.DampedTwistEdgeSubstitution
import GaloisForLFunctions.RHTower.Sieve.DampedSaving
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistConcreteEdges

/-!
# The twisted damped contour bound at the concrete rectangle

The twisted analogue of `Sieve/DampedContourBound`, equivalently the damped analogue of
`Sieve/MoebiusTwistContourBound`.  The contour geometry, the zero-free band and the four `invZeta`
edge estimates at the shifted heights are reused verbatim from the twisted Möbius argument; each of
them is multiplied by `dampedCorrBound P (leftAbscissa K)`, which dominates the Euler correction on
the whole rectangle uniformly in the damping parameter and in the twist, because the correction
depends only on the abscissa.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

/-- The left abscissa stays right of `1/2`. -/
theorem half_le_leftAbscissa {K : ℕ} (hlogK : (3 : ℝ) ≤ Real.log K) :
    1 / 2 ≤ leftAbscissa K := by
  rw [leftAbscissa]; linarith [leftAbscissa_gap_small hlogK]

/-- A local Euler factor is continuous along a shifted vertical line. -/
theorem continuous_dampedEulerFactorTwist_line {p : ℕ} (hp : 2 ≤ p) (t : ℝ) (τ : ℝ) {d : ℝ}
    (hd : 0 < d) :
    Continuous
      (fun y : ℝ =>
        dampedEulerFactor t p ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)) := by
  have hfun :
      (fun y : ℝ => dampedEulerFactor t p ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        = (fun y : ℝ => dampedEulerFactor t p ((d : ℂ) + (y : ℝ) * Complex.I))
          ∘ fun y : ℝ => y + τ := by
    funext y
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact (continuous_dampedEulerFactor_line hp t hd).comp (continuous_id.add continuous_const)

/-- The damped integrand is continuous on the shifted left edge. -/
theorem continuousOn_dampedInvZetaTwist_left_line {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) (t : ℝ)
    {c d T : ℝ} (τ : ℝ) (hT : 0 ≤ T) (hc0 : 0 < c) (hcd : c ≤ 1) (hd1 : 1 ≤ d)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    ContinuousOn
      (fun y : ℝ => dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-T) T) := by
  have hfun :
      (fun y : ℝ => dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        = fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
            * ∏ p ∈ P, dampedEulerFactor t p
                ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by
    funext y; rw [dampedInvZeta]
  rw [hfun]
  exact (continuousOn_invZetaTwist_left_line τ hT hcd hd1 hzf).mul
    ((continuous_finsetProd P
      (fun p hp => continuous_dampedEulerFactorTwist_line (hP p hp) t τ hc0)).continuousOn)

/-- **The twisted damped contour bound.**  Unconditional: for all large `K` and every twist with
`5 + 4|τ| ≤ K`, the twisted damped smoothed sum is bounded by the four edge contributions at the
concrete rectangle, each carrying the same Euler correction factor. -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le_concrete {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) (j : ℕ) :
    ∃ (C M₀ : ℝ) (K₀ : ℕ), 0 ≤ C ∧ 0 ≤ M₀ ∧ ∀ (τ : ℝ) (K : ℕ), K₀ ≤ K → 5 + 4 * |τ| ≤ (K : ℝ) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * ((invZetaRightBound K * dampedCorrBound P (leftAbscissa K)) * C) / twistHeight K τ
            + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K)) * C
                / (twistHeight K τ) ^ (j + 1) * (rightAbscissa K - leftAbscissa K)
            + (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K)) * C
                / (twistHeight K τ) ^ (j + 1) * (rightAbscissa K - leftAbscissa K)
            + (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
                * (2 * ((N + H) ^ leftAbscissa K / leftAbscissa K) + 2 * C) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C, hC, hmain⟩ := exists_norm_tsum_dampedTwist_smoothWeight_le hPprime ht0 ht1 hN hH j 2
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
  refine ⟨C, M₀, max K₁ 5, hC, hM₀, fun τ K hKle hKτ => ?_⟩
  obtain ⟨hlogK, hfitpow⟩ := hK₁ K (le_trans (le_max_left _ _) hKle)
  have hK5 : 5 ≤ K := le_trans (le_max_right _ _) hKle
  have hK2 : 2 ≤ K := by omega
  have hδ0 : (0 : ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hL9 := twentySeven_le_log_pow hlogK
  have hfit : zeroFreeConst / (16 * (Real.log K) ^ 9) ≤ min δ₁ δ₂ := by
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
  -- the four damped edges, each the `invZeta` edge times the correction
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
  exact hmain τ (leftAbscissa K) (rightAbscissa K) (twistHeight K τ)
    (invZetaRightBound K * dampedCorrBound P (leftAbscissa K))
    (invZetaEdgeBound K * dampedCorrBound P (leftAbscissa K))
    (max M₀ (invZetaEdgeBound K) * dampedCorrBound P (leftAbscissa K))
    (one_lt_rightAbscissa hlogK) (rightAbscissa_le_two hlogK) (leftAbscissa_pos hlogK) hcd hT1
    (mul_nonneg (invZetaRightBound_nonneg K) hcorr0)
    (mul_nonneg (invZetaEdgeBound_nonneg K) hcorr0)
    (mul_nonneg (le_trans hM₀ (le_max_left _ _)) hcorr0) hzf hFd hFt hFb hFc hFccont

end

end RHTower.Sieve
