import GaloisForLFunctions.Bottcher.RepellingFixedPreimageSelector
import GaloisForLFunctions.Bottcher.ZeroSurvival

open Polynomial Filter Topology Set Metric

namespace Bottcher

noncomputable section

/-- Derivative of the true fixed-tail displacement at a forward hit to a fixed point. -/
theorem deriv_displacement_fixed_tail_of_iterate_eq_fixed
    {c z α : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α) (m : ℕ) :
    deriv (fun w => (quadratic c)^[n + m] w - w) z =
      (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) * ((2 : ℂ) * α) ^ m - 1 := by
  have hderiv :
      deriv (fun w => (quadratic c)^[n + m] w - w) z =
        deriv ((quadratic c)^[n + m]) z - 1 := by
    have hF : HasDerivAt (fun w => (quadratic c)^[n + m] w - w)
        (deriv ((quadratic c)^[n + m]) z - 1) z :=
      ((differentiable_quadratic_iterate_repellingFixedPoint c (n + m)).differentiableAt.hasDerivAt).sub
        (hasDerivAt_id z)
    exact hF.deriv
  rw [hderiv, deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m]

/-- For a noncritical hit to a repelling fixed point, the inverse derivative of the true
displacement `f_c^[n+m] - id` tends to zero along the fixed tail. -/
theorem eventually_tail_displacement_deriv_inv_norm_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      deriv (fun w => (quadratic c)^[n + m] w - w) z ≠ 0 ∧
      ‖(deriv (fun w => (quadratic c)^[n + m] w - w) z)⁻¹‖ < ε := by
  have htend := tendsto_norm_deriv_fixed_tail_atTop hhit hfix hinit hrep
  have hev : ∀ᶠ m : ℕ in atTop,
      ε⁻¹ + 1 < ‖deriv ((quadratic c)^[n + m]) z‖ :=
    htend.eventually_gt_atTop (ε⁻¹ + 1)
  filter_upwards [hev] with m hm
  have hdisp :
      deriv (fun w => (quadratic c)^[n + m] w - w) z =
        deriv ((quadratic c)^[n + m]) z - 1 := by
    have hF : HasDerivAt (fun w => (quadratic c)^[n + m] w - w)
        (deriv ((quadratic c)^[n + m]) z - 1) z :=
      ((differentiable_quadratic_iterate_repellingFixedPoint c (n + m)).differentiableAt.hasDerivAt).sub
        (hasDerivAt_id z)
    exact hF.deriv
  have hlarge : ε⁻¹ < ‖deriv ((quadratic c)^[n + m]) z - 1‖ := by
    have htriangle :
        ‖deriv ((quadratic c)^[n + m]) z‖ ≤
          ‖deriv ((quadratic c)^[n + m]) z - 1‖ + 1 := by
      calc
        ‖deriv ((quadratic c)^[n + m]) z‖ =
            ‖(deriv ((quadratic c)^[n + m]) z - 1) + 1‖ := by ring_nf
        _ ≤ ‖deriv ((quadratic c)^[n + m]) z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖deriv ((quadratic c)^[n + m]) z - 1‖ + 1 := by norm_num
    by_contra hnot
    have hle : ‖deriv ((quadratic c)^[n + m]) z - 1‖ ≤ ε⁻¹ := le_of_not_gt hnot
    linarith
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have hnormpos : 0 < ‖deriv ((quadratic c)^[n + m]) z - 1‖ := lt_trans hεinv hlarge
  have hderiv_ne :
      deriv (fun w => (quadratic c)^[n + m] w - w) z ≠ 0 := by
    rw [hdisp]
    exact norm_pos_iff.mp hnormpos
  refine ⟨hderiv_ne, ?_⟩
  rw [hdisp, norm_inv]
  exact (inv_lt_comm₀ hnormpos hε).2 hlarge

/-- Along a noncritical hit to a repelling fixed point, the Newton center-size factor for the true
displacement is eventually below every positive threshold. -/
theorem eventually_tail_displacement_inv_deriv_mul_fixed_dist_lt_of_repelling_hit
    {c z α : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      deriv (fun w => (quadratic c)^[n + m] w - w) z ≠ 0 ∧
      ‖(deriv (fun w => (quadratic c)^[n + m] w - w) z)⁻¹‖ * ‖α - z‖ < η := by
  by_cases hαz : α = z
  · have hev :=
      eventually_tail_displacement_deriv_inv_norm_lt_of_repelling_hit
        hhit hfix hinit hrep (show (0 : ℝ) < 1 by norm_num)
    filter_upwards [hev] with m hm
    refine ⟨hm.1, ?_⟩
    rw [hαz, sub_self, norm_zero, mul_zero]
    exact hη
  · have hdistpos : 0 < ‖α - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hαz)
    have hε : 0 < η / ‖α - z‖ := div_pos hη hdistpos
    have hev :=
      eventually_tail_displacement_deriv_inv_norm_lt_of_repelling_hit
        hhit hfix hinit hrep hε
    filter_upwards [hev] with m hm
    refine ⟨hm.1, ?_⟩
    have hmul :
        ‖(deriv (fun w => (quadratic c)^[n + m] w - w) z)⁻¹‖ * ‖α - z‖ <
          (η / ‖α - z‖) * ‖α - z‖ :=
      mul_lt_mul_of_pos_right hm.2 hdistpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hdistpos)] at hmul

/-- Derivative of the scaled displacement used by the Poincare/Hurwitz window. -/
theorem deriv_scaled_displacement
    (c z scale τ : ℂ) (q : ℕ) :
    deriv (fun t => (quadratic c)^[q] (z + scale * t) - (z + scale * t)) τ =
      scale * (deriv ((quadratic c)^[q]) (z + scale * τ) - 1) := by
  have hL0 := (hasDerivAt_const τ z).add (hasDerivAt_const_mul (x := τ) scale)
  have hL : HasDerivAt (fun t : ℂ => z + scale * t) scale τ := by
    simpa only [Pi.add_apply, zero_add] using! hL0
  have hF : HasDerivAt ((quadratic c)^[q])
      (deriv ((quadratic c)^[q]) (z + scale * τ)) (z + scale * τ) :=
    ((differentiable_quadratic_iterate_repellingFixedPoint c q).differentiableAt).hasDerivAt
  have hG : HasDerivAt (fun w => (quadratic c)^[q] w - w)
      (deriv ((quadratic c)^[q]) (z + scale * τ) - 1) (z + scale * τ) :=
    hF.sub (hasDerivAt_id (z + scale * τ))
  have hcomp := hG.comp τ hL
  have hderiv :
      deriv (fun t => (quadratic c)^[q] (z + scale * t) - (z + scale * t)) τ =
        (deriv ((quadratic c)^[q]) (z + scale * τ) - 1) * scale := by
    simpa only [Function.comp_apply] using! hcomp.deriv
  rw [hderiv]
  ring

/-- If the scale is the inverse multiplier at the base point, the scaled displacement derivative at
`0` is exactly `1 - (f_c^[q])'(z)⁻¹`. -/
theorem deriv_scaled_displacement_inv_deriv_at_zero
    {c z : ℂ} {q : ℕ}
    (hD : deriv ((quadratic c)^[q]) z ≠ 0) :
    deriv
        (fun t => (quadratic c)^[q] (z + (deriv ((quadratic c)^[q]) z)⁻¹ * t) -
          (z + (deriv ((quadratic c)^[q]) z)⁻¹ * t)) 0 =
      1 - (deriv ((quadratic c)^[q]) z)⁻¹ := by
  rw [deriv_scaled_displacement]
  simp only [mul_zero, add_zero]
  field_simp [hD]

/-- If `u` is within `1/2` of `0`, then `1-u` is nonzero and its inverse has norm at most `2`. -/
theorem one_sub_inv_norm_le_two_of_norm_lt_half {u : ℂ}
    (hu : ‖u‖ < (1 / 2 : ℝ)) :
    (1 - u) ≠ 0 ∧ ‖(1 - u)⁻¹‖ ≤ (2 : ℝ) := by
  have htri : ‖(1 : ℂ)‖ ≤ ‖1 - u‖ + ‖u‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      norm_add_le (1 - u) u
  have hhalf : (1 / 2 : ℝ) < ‖1 - u‖ := by
    norm_num at htri
    linarith
  have hpos : 0 < ‖1 - u‖ := by linarith
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [norm_inv]
  have hlt : (‖1 - u‖)⁻¹ < (2 : ℝ) := by
    have hhalfpos : 0 < (1 / 2 : ℝ) := by norm_num
    have := (inv_lt_inv₀ hpos hhalfpos).2 hhalf
    norm_num at this
    exact this
  exact le_of_lt hlt

/-- Along a noncritical repelling fixed tail, the scaled displacement with inverse-multiplier scale
has center derivative bounded away from zero and inverse derivative bounded by `2`, eventually. -/
theorem eventually_scaled_displacement_deriv_at_zero_inv_norm_le_two_of_repelling_hit
    {c z α : ℂ} {n : ℕ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖) :
    ∀ᶠ m : ℕ in atTop,
      let D := deriv ((quadratic c)^[n + m]) z
      D ≠ 0 ∧
        deriv (fun t => (quadratic c)^[n + m] (z + D⁻¹ * t) - (z + D⁻¹ * t)) 0 ≠ 0 ∧
        ‖(deriv (fun t => (quadratic c)^[n + m] (z + D⁻¹ * t) -
          (z + D⁻¹ * t)) 0)⁻¹‖ ≤ (2 : ℝ) := by
  have htend := tendsto_norm_deriv_fixed_tail_atTop hhit hfix hinit hrep
  have hev : ∀ᶠ m : ℕ in atTop,
      (1 / 2 : ℝ)⁻¹ < ‖deriv ((quadratic c)^[n + m]) z‖ :=
    htend.eventually_gt_atTop (1 / 2 : ℝ)⁻¹
  filter_upwards [hev] with m hm
  let D := deriv ((quadratic c)^[n + m]) z
  have hhalfpos : 0 < (1 / 2 : ℝ) := by norm_num
  have hhalf_inv_pos : 0 < (1 / 2 : ℝ)⁻¹ := inv_pos.mpr hhalfpos
  have hDnormpos : 0 < ‖D‖ := by
    dsimp [D]
    exact lt_trans hhalf_inv_pos hm
  have hDne : D ≠ 0 := norm_pos_iff.mp hDnormpos
  have hDinv_lt : ‖D⁻¹‖ < (1 / 2 : ℝ) := by
    rw [norm_inv]
    exact (inv_lt_comm₀ hDnormpos hhalfpos).2 (by simpa [D] using hm)
  have hscaled :
      deriv (fun t => (quadratic c)^[n + m] (z + D⁻¹ * t) - (z + D⁻¹ * t)) 0 =
        1 - D⁻¹ := by
    dsimp [D]
    exact deriv_scaled_displacement_inv_deriv_at_zero hDne
  have hbound := one_sub_inv_norm_le_two_of_norm_lt_half (u := D⁻¹) hDinv_lt
  refine ⟨hDne, ?_, ?_⟩
  · rw [hscaled]
    exact hbound.1
  · rw [hscaled]
    exact hbound.2

/-- Fixed-tail constructor for the scaled inverse-derivative window at scaled center `0`.

The caller supplies only the geometric containment of the inverse-multiplier scaled ball and the
scaled derivative-variation estimate.  The derivative nonvanishing, inverse-derivative bound, and
center fit are consequences of the repelling fixed tail. -/
theorem eventually_scaled_inv_deriv_window_at_zero_of_variation
    {c ζ z α : ℂ} {n : ℕ} {R r μ : ℝ} {K : NNReal}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hr : 0 ≤ r) (hμ : 0 ≤ μ) (hK : K < 1)
    (hcenter_margin : (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r)
    (hsmall_margin : (2 : ℝ) * μ ≤ (K : ℝ))
    (hcontain : ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t ∈ Metric.ball ζ R)
    (hvar : ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        ‖deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
          deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ (τ scale : ℂ) (r' μ' : ℝ) (K' : NNReal),
        0 ≤ r' ∧ 0 ≤ μ' ∧
        deriv
          (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ ≠ 0 ∧
        (∀ t ∈ Metric.closedBall τ r', z + scale * t ∈ Metric.ball ζ R) ∧
        K' < 1 ∧
        ‖(deriv
          (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹‖ *
          ‖(quadratic c)^[n + m] (z + scale * τ) - (z + scale * τ)‖ ≤
            (1 - (K' : ℝ)) * r' ∧
        (∀ t ∈ Metric.closedBall τ r',
          ‖deriv
              (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) t -
            deriv
              (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) τ‖ ≤ μ') ∧
        ‖(deriv
          (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹‖ *
            μ' ≤ (K' : ℝ) := by
  have hderiv :=
    eventually_scaled_displacement_deriv_at_zero_inv_norm_le_two_of_repelling_hit
      hhit hfix hinit hrep
  filter_upwards [hderiv, hcontain, hvar] with m hderiv_m hcontain_m hvar_m
  let D := deriv ((quadratic c)^[n + m]) z
  let S : ℂ → ℂ := fun t => (quadratic c)^[n + m] (z + D⁻¹ * t) - (z + D⁻¹ * t)
  refine ⟨0, D⁻¹, r, μ, K, hr, hμ, ?_, ?_, hK, ?_, ?_, ?_⟩
  · dsimp [S, D] at hderiv_m ⊢
    exact hderiv_m.2.1
  · simpa [D] using hcontain_m
  · have htail : (quadratic c)^[n + m] z = α :=
      iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m
    have hnorm_le :
        ‖(deriv (fun t => (quadratic c)^[n + m] (z + D⁻¹ * t) -
          (z + D⁻¹ * t)) 0)⁻¹‖ * ‖α - z‖ ≤ (2 : ℝ) * ‖α - z‖ :=
      mul_le_mul_of_nonneg_right hderiv_m.2.2 (norm_nonneg _)
    dsimp [D]
    rw [mul_zero, add_zero, htail]
    exact le_trans hnorm_le hcenter_margin
  · simpa [D] using hvar_m
  · have hsmall_le :
        ‖(deriv (fun t => (quadratic c)^[n + m] (z + D⁻¹ * t) -
          (z + D⁻¹ * t)) 0)⁻¹‖ * μ ≤ (2 : ℝ) * μ :=
      mul_le_mul_of_nonneg_right hderiv_m.2.2 hμ
    dsimp [D]
    exact le_trans hsmall_le hsmall_margin

/-- Fixed-radius constructor for the true-displacement Newton window.

Once the normalized derivative variation of `f_c^[n+m] - id` is eventually bounded by `K < 1` on a
fixed closed ball, the repelling fixed tail supplies the missing center estimate automatically. -/
theorem eventually_displacement_newton_window_of_fixed_radius_variation
    {c z α : ℂ} {n : ℕ} {R r μ : ℝ} {K : NNReal}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hrpos : 0 < r) (hrle : r ≤ R / 2) (hμ : 0 ≤ μ) (hK : K < 1)
    (hvar : ∀ᶠ m : ℕ in atTop,
      ∀ y ∈ Metric.closedBall z r,
        ‖deriv (fun w => (quadratic c)^[n + m] w - w) y -
          deriv (fun w => (quadratic c)^[n + m] w - w) z‖ ≤ μ)
    (hsmall : ∀ᶠ m : ℕ in atTop,
      ‖(deriv (fun w => (quadratic c)^[n + m] w - w) z)⁻¹‖ * μ ≤ (K : ℝ)) :
    ∀ᶠ m : ℕ in atTop,
      ∃ (r' μ' : ℝ) (K' : NNReal) (A : ℂ),
        0 ≤ r' ∧ r' ≤ R / 2 ∧ 0 ≤ μ' ∧ A ≠ 0 ∧
        A * deriv (fun w => (quadratic c)^[n + m] w - w) z = 1 ∧
        K' < 1 ∧
        ‖A‖ * ‖(quadratic c)^[n + m] z - z‖ ≤ (1 - (K' : ℝ)) * r' ∧
        (∀ y ∈ Metric.closedBall z r',
          ‖deriv (fun w => (quadratic c)^[n + m] w - w) y -
            deriv (fun w => (quadratic c)^[n + m] w - w) z‖ ≤ μ') ∧
        ‖A‖ * μ' ≤ (K' : ℝ) := by
  have heta : 0 < (1 - (K : ℝ)) * r := by
    have hKpos : 0 < 1 - (K : ℝ) := by exact sub_pos.mpr hK
    exact mul_pos hKpos hrpos
  have hcenter :=
    eventually_tail_displacement_inv_deriv_mul_fixed_dist_lt_of_repelling_hit
      hhit hfix hinit hrep heta
  filter_upwards [hcenter, hvar, hsmall] with m hcenter_m hvar_m hsmall_m
  let D : ℂ := deriv (fun w => (quadratic c)^[n + m] w - w) z
  refine ⟨r, μ, K, D⁻¹, le_of_lt hrpos, hrle, hμ, inv_ne_zero hcenter_m.1, ?_,
    hK, ?_, hvar_m, hsmall_m⟩
  · dsimp [D]
    exact inv_mul_cancel₀ hcenter_m.1
  · have htail : (quadratic c)^[n + m] z = α :=
      iterate_add_eq_fixed_of_iterate_eq_fixed hhit hfix m
    dsimp [D] at hcenter_m ⊢
    rw [htail]
    exact le_of_lt hcenter_m.2

/-- Repelling-fixed selector bridge using the true displacement `f_c^[q] - id`.

This is the local hRigid interface for the Poincare/Hurwitz route: after the selector produces a
nontrivial positive forward hit `f_c^[n] z = α`, the caller only has to supply an eventual Newton
window for the displacement of the return map itself.  No separate no-precritical or fixed-tail
second-derivative hypothesis is needed. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_displacement_newton_window_half
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (r μ : ℝ) (K : NNReal) (A : ℂ),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ μ ∧ A ≠ 0 ∧
            A * deriv (fun w => (quadratic c)^[n + m] w - w) z = 1 ∧
            K < 1 ∧
            ‖A‖ * ‖(quadratic c)^[n + m] z - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => (quadratic c)^[n + m] w - w) y -
                deriv (fun w => (quadratic c)^[n + m] w - w) z‖ ≤ μ) ∧
            ‖A‖ * μ ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_preimage_pair_to_positive_periodic_half
    hαfix (fixed_point_ne_zero_of_repelling hαrep)
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  by_cases hzα : z = α
  · subst z
    have hαR : α ∈ Metric.ball z₀ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨α, hαR, 1, by norm_num, by simpa using hαfix⟩
  · have hzfrontHit : z ∈ frontier (filledJulia c) :=
      mem_frontier_of_forward_hit_repelling_fixed (c := c) (z := z) (α := α) (n := n)
        hhit hαfix hαrep
    have hwin := hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
    obtain ⟨m, hm⟩ := eventually_atTop.mp hwin
    rcases hm m le_rfl with
      ⟨r, μ, K, A, hr, hrle, _hμ, hA, hAinv, hK, hcenter, hvar, hsmall⟩
    have hq : 1 ≤ n + m := by omega
    exact exists_positive_periodic_mem_ball_of_displacement_newton_deriv_variation
      (c := c) (ζ := z₀) (a := z) (A := A) (q := n + m)
      (R := R) (r := r) (μ := μ) (K := K)
      hq hA hAinv hr hK
      (closedBall_subset_ball_of_mem_ball_half_radius_le hz hrle)
      hcenter hvar hsmall

/-- Selector bridge where the local input is a fixed-radius normalized-variation estimate for the
true displacement.  The non-postcritical anchor condition supplies noncriticality of every forward
hit, and the center estimate is discharged by the repelling fixed tail. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_fixed_radius_displacement_window_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal),
          0 < r ∧ r ≤ R / 2 ∧ 0 ≤ μ ∧ K < 1 ∧
          ∀ᶠ m : ℕ in atTop,
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => (quadratic c)^[n + m] w - w) y -
                deriv (fun w => (quadratic c)^[n + m] w - w) z‖ ≤ μ) ∧
            ‖(deriv (fun w => (quadratic c)^[n + m] w - w) z)⁻¹‖ * μ ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_displacement_newton_window_half
    hαfix hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨r, μ, K, hrpos, hrle, hμ, hK, hev⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
    (orbitProduct_ne_zero_iff_no_precritical c z n).2
      (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit)
  exact eventually_displacement_newton_window_of_fixed_radius_variation
    (c := c) (z := z) (α := α) (n := n) (R := R) (r := r) (μ := μ) (K := K)
    hhit hαfix hinit hαrep hrpos hrle hμ hK
    (hev.mono (fun _ hm => hm.1))
    (hev.mono (fun _ hm => hm.2))

/-- Repelling-fixed selector bridge using a scaled displacement Newton/Hurwitz window.

This is the interface for the Poincare coordinate route: the zero is produced in a scaled variable
`t`, then mapped back to `z + scale * t` in the original plane.  The caller supplies the scaled
closed-ball containment in the requested frontier ball. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_window_half
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (τ scale A : ℂ) (r μ : ℝ) (K : NNReal),
            0 ≤ r ∧ 0 ≤ μ ∧ A ≠ 0 ∧
            (∀ t ∈ Metric.closedBall τ r, z + scale * t ∈ Metric.ball z₀ R) ∧
            A * deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ = 1 ∧
            K < 1 ∧
            ‖A‖ *
              ‖(quadratic c)^[n + m] (z + scale * τ) - (z + scale * τ)‖ ≤
                (1 - (K : ℝ)) * r ∧
            (∀ t ∈ Metric.closedBall τ r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) τ‖ ≤ μ) ∧
            ‖A‖ * μ ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_preimage_pair_to_positive_periodic_half
    hαfix (fixed_point_ne_zero_of_repelling hαrep)
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  by_cases hzα : z = α
  · subst z
    have hαR : α ∈ Metric.ball z₀ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨α, hαR, 1, by norm_num, by simpa using hαfix⟩
  · have hzfrontHit : z ∈ frontier (filledJulia c) :=
      mem_frontier_of_forward_hit_repelling_fixed (c := c) (z := z) (α := α) (n := n)
        hhit hαfix hαrep
    have hwin := hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
    obtain ⟨m, hm⟩ := eventually_atTop.mp hwin
    rcases hm m le_rfl with
      ⟨τ, scale, A, r, μ, K, hr, hμ, hA, hscale, hAinv, hK, hcenter, hvar, hsmall⟩
    have hq : 1 ≤ n + m := by omega
    exact exists_positive_periodic_mem_ball_of_scaled_displacement_newton_deriv_variation
      (c := c) (ζ := z₀) (z := z) (τ := τ) (scale := scale) (A := A)
      (q := n + m) (R := R) (r := r) (μ := μ) (K := K)
      hq hA hAinv hr hK hscale hcenter hvar hsmall

/-- Scaled selector bridge with the natural inverse-derivative data.  This removes the explicit
coefficient `A` from the caller: the Newton coefficient is canonically the inverse derivative of the
scaled displacement at the scaled base point. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_inv_deriv_window_half
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (τ scale : ℂ) (r μ : ℝ) (K : NNReal),
            0 ≤ r ∧ 0 ≤ μ ∧
            deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ ≠ 0 ∧
            (∀ t ∈ Metric.closedBall τ r, z + scale * t ∈ Metric.ball z₀ R) ∧
            K < 1 ∧
            ‖(deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m] (z + scale * τ) - (z + scale * τ)‖ ≤
                (1 - (K : ℝ)) * r ∧
            (∀ t ∈ Metric.closedBall τ r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) τ‖ ≤ μ) ∧
            ‖(deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_window_half
    hαfix hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  exact (hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit).mono (by
    intro m hm
    rcases hm with
      ⟨τ, scale, r, μ, K, hr, hμ, hderiv, hscale, hK, hcenter, hvar, hsmall⟩
    refine ⟨τ, scale,
      (deriv (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹,
      r, μ, K, hr, hμ, inv_ne_zero hderiv, hscale, ?_, hK, hcenter, hvar, hsmall⟩
    exact inv_mul_cancel₀ hderiv)

/-- Selector bridge for the inverse-multiplier scaled window centered at `0`.

The remaining local work is now exactly the scaled-ball containment and scaled derivative-variation
estimate.  The fixed-tail derivative growth supplies derivative nonvanishing, inverse-derivative
control, and the Newton center fit. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
          (2 : ℝ) * μ ≤ (K : ℝ) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall (0 : ℂ) r,
              z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t ∈ Metric.ball z₀ R) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall (0 : ℂ) r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_inv_deriv_window_half
    hαfix hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨r, μ, K, hr, hμ, hK, hcenter, hsmall, hcontain, hvar⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
    (orbitProduct_ne_zero_iff_no_precritical c z n).2
      (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit)
  exact eventually_scaled_inv_deriv_window_at_zero_of_variation
    (c := c) (ζ := z₀) (z := z) (α := α) (n := n)
    (R := R) (r := r) (μ := μ) (K := K)
    hhit hαfix hinit hαrep hr hμ hK hcenter hsmall hcontain hvar

/-- q62 target-density reduction from the repelling-fixed selector and a true-displacement Newton
window.  This is the current hRigid endpoint for the zero-survival route; the remaining analytic
work is to construct the `hwindow` estimates. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_displacement_newton_window_half_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (r μ : ℝ) (K : NNReal) (A : ℂ),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ μ ∧ A ≠ 0 ∧
            A * deriv (fun w => (quadratic c)^[n + m] w - w) z = 1 ∧
            K < 1 ∧
            ‖A‖ * ‖(quadratic c)^[n + m] z - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => (quadratic c)^[n + m] w - w) y -
                deriv (fun w => (quadratic c)^[n + m] w - w) z‖ ≤ μ) ∧
            ‖A‖ * μ ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_displacement_newton_window_half
      hαfix hαrep hwindow)
    hE

/-- q62 target-density reduction from fixed-radius normalized-variation estimates for the true
displacement.  Compared with the explicit scaled fixed-tail route, the center estimate has been
removed from the caller obligations. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_fixed_radius_displacement_window_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal),
          0 < r ∧ r ≤ R / 2 ∧ 0 ≤ μ ∧ K < 1 ∧
          ∀ᶠ m : ℕ in atTop,
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => (quadratic c)^[n + m] w - w) y -
                deriv (fun w => (quadratic c)^[n + m] w - w) z‖ ≤ μ) ∧
            ‖(deriv (fun w => (quadratic c)^[n + m] w - w) z)⁻¹‖ * μ ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_fixed_radius_displacement_window_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

/-- q62 target-density reduction using the scaled displacement zero-survival window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_displacement_window_half_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (τ scale A : ℂ) (r μ : ℝ) (K : NNReal),
            0 ≤ r ∧ 0 ≤ μ ∧ A ≠ 0 ∧
            (∀ t ∈ Metric.closedBall τ r, z + scale * t ∈ Metric.ball z₀ R) ∧
            A * deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ = 1 ∧
            K < 1 ∧
            ‖A‖ *
              ‖(quadratic c)^[n + m] (z + scale * τ) - (z + scale * τ)‖ ≤
                (1 - (K : ℝ)) * r ∧
            (∀ t ∈ Metric.closedBall τ r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) τ‖ ≤ μ) ∧
            ‖A‖ * μ ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_window_half
      hαfix hαrep hwindow)
    hE

/-- q62 target-density reduction using the scaled inverse-derivative window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_displacement_inv_deriv_window_half_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (τ scale : ℂ) (r μ : ℝ) (K : NNReal),
            0 ≤ r ∧ 0 ≤ μ ∧
            deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ ≠ 0 ∧
            (∀ t ∈ Metric.closedBall τ r, z + scale * t ∈ Metric.ball z₀ R) ∧
            K < 1 ∧
            ‖(deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m] (z + scale * τ) - (z + scale * τ)‖ ≤
                (1 - (K : ℝ)) * r ∧
            (∀ t ∈ Metric.closedBall τ r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m] (z + scale * u) - (z + scale * u)) τ‖ ≤ μ) ∧
            ‖(deriv
              (fun t => (quadratic c)^[n + m] (z + scale * t) - (z + scale * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_inv_deriv_window_half
      hαfix hαrep hwindow)
    hE

/-- q62 target-density reduction from the inverse-multiplier scaled window centered at `0`. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_at_zero_variation_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
          (2 : ℝ) * μ ≤ (K : ℝ) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall (0 : ℂ) r,
              z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t ∈ Metric.ball z₀ R) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall (0 : ℂ) r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

end

end Bottcher
