import GaloisForLFunctions.Bottcher.RepellingFixedZeroSurvival

open Polynomial Filter Topology Set Metric

namespace Bottcher

noncomputable section

/-- Inverse-multiplier scaled balls around a forward hit eventually lie in the requested target ball.

If `z` is already in the half-radius target ball, then the repelling fixed tail makes
`((f_c^[n+m])' z)⁻¹` arbitrarily small. Hence every fixed scaled closed ball maps into the original
target ball under `t ↦ z + ((f_c^[n+m])' z)⁻¹ t`, eventually. -/
theorem eventually_inverse_scaled_closedBall_subset_ball_of_repelling_hit
    {c ζ z α : ℂ} {n : ℕ} {R r : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hz : z ∈ Metric.ball ζ (R / 2)) (hr : 0 ≤ r) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t ∈ Metric.ball ζ R := by
  rw [Metric.mem_ball] at hz
  have hRhalf : 0 < R / 2 := lt_of_le_of_lt dist_nonneg hz
  let ε : ℝ := (R / 2) / (r + 1)
  have hr1 : 0 < r + 1 := by linarith
  have hε : 0 < ε := div_pos hRhalf hr1
  have htend := tendsto_norm_deriv_fixed_tail_atTop hhit hfix hinit hrep
  have hev : ∀ᶠ m : ℕ in atTop,
      ε⁻¹ < ‖deriv ((quadratic c)^[n + m]) z‖ :=
    htend.eventually_gt_atTop ε⁻¹
  filter_upwards [hev] with m hm t ht
  let D : ℂ := deriv ((quadratic c)^[n + m]) z
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have hDnormpos : 0 < ‖D‖ := by
    dsimp [D]
    exact lt_trans hεinv hm
  have hinvlt : ‖D⁻¹‖ < ε := by
    rw [norm_inv]
    exact (inv_lt_comm₀ hDnormpos hε).2 (by simpa [D] using hm)
  have ht_norm : ‖t‖ ≤ r := by
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    simpa using ht
  have hstep_le : dist (z + D⁻¹ * t) z ≤ R / 2 := by
    have hmul : ‖D⁻¹ * t‖ ≤ ε * r := by
      rw [norm_mul]
      exact mul_le_mul (le_of_lt hinvlt) ht_norm (norm_nonneg _) (le_of_lt hε)
    have hεr : ε * r ≤ R / 2 := by
      have hrle : r ≤ r + 1 := by linarith
      calc
        ε * r ≤ ε * (r + 1) := mul_le_mul_of_nonneg_left hrle (le_of_lt hε)
        _ = R / 2 := by
          dsimp [ε]
          rw [div_mul_cancel₀ _ (ne_of_gt hr1)]
    calc
      dist (z + D⁻¹ * t) z = ‖D⁻¹ * t‖ := by
        rw [dist_eq_norm]
        congr 1
        ring
      _ ≤ ε * r := hmul
      _ ≤ R / 2 := hεr
  rw [Metric.mem_ball]
  calc
    dist (z + D⁻¹ * t) ζ ≤ dist (z + D⁻¹ * t) z + dist z ζ := dist_triangle _ _ _
    _ ≤ R / 2 + dist z ζ := by
      simpa [add_comm] using add_le_add_left hstep_le (dist z ζ)
    _ < R / 2 + R / 2 := add_lt_add_of_le_of_lt le_rfl hz
    _ = R := by ring

/-- Transfer an unscaled derivative-variation bound on the tiny physical ball to the scaled
derivative-variation bound in the inverse-multiplier coordinate. -/
theorem scaled_deriv_variation_le_of_physical_deriv_variation
    {c z : ℂ} {q : ℕ} {r M μ : ℝ}
    (hphys : ∀ w ∈ Metric.closedBall z
        (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r),
      ‖deriv ((quadratic c)^[q]) w - deriv ((quadratic c)^[q]) z‖ ≤ M)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * M ≤ μ) :
    ∀ t ∈ Metric.closedBall (0 : ℂ) r,
      ‖deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) t -
        deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) 0‖ ≤ μ := by
  intro t ht
  let D : ℂ := deriv ((quadratic c)^[q]) z
  let w : ℂ := z + D⁻¹ * t
  have ht_norm : ‖t‖ ≤ r := by
    rw [Metric.mem_closedBall, dist_eq_norm] at ht
    simpa using ht
  have hw : w ∈ Metric.closedBall z (‖D⁻¹‖ * r) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hmul : ‖D⁻¹ * t‖ ≤ ‖D⁻¹‖ * r := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ht_norm (norm_nonneg _)
    calc
      ‖w - z‖ = ‖D⁻¹ * t‖ := by
        dsimp [w]
        congr 1
        ring
      _ ≤ ‖D⁻¹‖ * r := hmul
  have hdt :
      deriv
          (fun u => (quadratic c)^[q] (z + D⁻¹ * u) - (z + D⁻¹ * u)) t =
        D⁻¹ * (deriv ((quadratic c)^[q]) w - 1) := by
    dsimp [w, D]
    exact deriv_scaled_displacement c z ((deriv ((quadratic c)^[q]) z)⁻¹) t q
  have hd0 :
      deriv
          (fun u => (quadratic c)^[q] (z + D⁻¹ * u) - (z + D⁻¹ * u)) 0 =
        D⁻¹ * (deriv ((quadratic c)^[q]) z - 1) := by
    have h :=
      deriv_scaled_displacement c z ((deriv ((quadratic c)^[q]) z)⁻¹) (0 : ℂ) q
    dsimp [D] at h ⊢
    simpa using h
  dsimp [D] at hdt hd0
  rw [hdt, hd0]
  have hdiff :
      (deriv ((quadratic c)^[q]) z)⁻¹ *
          (deriv ((quadratic c)^[q]) w - 1) -
        (deriv ((quadratic c)^[q]) z)⁻¹ *
          (deriv ((quadratic c)^[q]) z - 1) =
        (deriv ((quadratic c)^[q]) z)⁻¹ *
          (deriv ((quadratic c)^[q]) w - deriv ((quadratic c)^[q]) z) := by
    ring
  rw [hdiff, norm_mul]
  exact le_trans
    (mul_le_mul_of_nonneg_left (hphys w (by simpa [D] using hw)) (norm_nonneg _))
    hsmall

/-- Eventual form of `scaled_deriv_variation_le_of_physical_deriv_variation`. -/
theorem eventually_scaled_deriv_variation_of_physical_deriv_variation
    {c z : ℂ} {n : ℕ} {r μ : ℝ} (M : ℕ → ℝ)
    (hphys : ∀ᶠ m : ℕ in atTop,
      ∀ w ∈ Metric.closedBall z
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
        ‖deriv ((quadratic c)^[n + m]) w -
          deriv ((quadratic c)^[n + m]) z‖ ≤ M m)
    (hsmall : ∀ᶠ m : ℕ in atTop,
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * M m ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        ‖deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
          deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ := by
  filter_upwards [hphys, hsmall] with m hphys_m hsmall_m
  exact scaled_deriv_variation_le_of_physical_deriv_variation
    (c := c) (z := z) (q := n + m) (r := r) (M := M m) (μ := μ)
    hphys_m hsmall_m

/-- A second-derivative bound on the shrinking physical ball gives the scaled derivative-variation
bound in inverse-multiplier coordinates. -/
theorem scaled_deriv_variation_le_of_second_deriv_bound
    {c z : ℂ} {q : ℕ} {r B μ : ℝ}
    (hr : 0 ≤ r)
    (hB : 0 ≤ B)
    (hsecond : ∀ y ∈ Metric.closedBall z
        (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r),
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ B)
    (hsmall :
      ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ *
        (B * (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ t ∈ Metric.closedBall (0 : ℂ) r,
      ‖deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) t -
        deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) 0‖ ≤ μ := by
  let ρ : ℝ := ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact mul_nonneg (norm_nonneg _) hr
  have hphys :
      ∀ y ∈ Metric.closedBall z ρ,
        ‖deriv ((quadratic c)^[q]) y - deriv ((quadratic c)^[q]) z‖ ≤ B * ρ :=
    deriv_variation_quadratic_iterate_le_of_second_deriv_bound_closedBall
      (c := c) (z := z) (q := q) (r := ρ) (M := B) hρ hB (by
        simpa [ρ] using hsecond)
  exact scaled_deriv_variation_le_of_physical_deriv_variation
    (c := c) (z := z) (q := q) (r := r) (M := B * ρ) (μ := μ)
    (by simpa [ρ] using hphys) (by simpa [ρ] using hsmall)

/-- Eventual form of `scaled_deriv_variation_le_of_second_deriv_bound`. -/
theorem eventually_scaled_deriv_variation_of_second_deriv_bound
    {c z : ℂ} {n : ℕ} {r μ : ℝ} (B : ℕ → ℝ)
    (hr : 0 ≤ r)
    (hB : ∀ᶠ m : ℕ in atTop, 0 ≤ B m)
    (hsecond : ∀ᶠ m : ℕ in atTop,
      ∀ y ∈ Metric.closedBall z
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
        ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B m)
    (hsmall : ∀ᶠ m : ℕ in atTop,
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
        (B m * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        ‖deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
          deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ := by
  filter_upwards [hB, hsecond, hsmall] with m hB_m hsecond_m hsmall_m
  exact scaled_deriv_variation_le_of_second_deriv_bound
    (c := c) (z := z) (q := n + m) (r := r) (B := B m) (μ := μ)
    hr hB_m hsecond_m hsmall_m

/-- Eventual existential form of `scaled_deriv_variation_le_of_second_deriv_bound`.

This is the fixed-tail interface needed in practice: at each tail length it is enough to produce
some nonnegative second-derivative bound on the shrinking physical ball satisfying the scalar
smallness inequality. -/
theorem eventually_scaled_deriv_variation_of_eventual_second_deriv_bound
    {c z : ℂ} {n : ℕ} {r μ : ℝ}
    (hr : 0 ≤ r)
    (hsecond : ∀ᶠ m : ℕ in atTop,
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall (0 : ℂ) r,
        ‖deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
          deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ := by
  filter_upwards [hsecond] with m hm
  rcases hm with ⟨B, hB, hbound, hsmall⟩
  exact scaled_deriv_variation_le_of_second_deriv_bound
    (c := c) (z := z) (q := n + m) (r := r) (B := B) (μ := μ)
    hr hB hbound hsmall

/-- Fixed-tail constructor for the scaled inverse-derivative window with containment discharged by
the inverse-multiplier shrinkage.  The caller now supplies only the margin inequalities and the
scaled derivative-variation estimate. -/
theorem eventually_scaled_inv_deriv_window_at_zero_of_variation_auto_containment
    {c ζ z α : ℂ} {n : ℕ} {R r μ : ℝ} {K : NNReal}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hz : z ∈ Metric.ball ζ (R / 2))
    (hr : 0 ≤ r) (hμ : 0 ≤ μ) (hK : K < 1)
    (hcenter_margin : (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r)
    (hsmall_margin : (2 : ℝ) * μ ≤ (K : ℝ))
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
            μ' ≤ (K' : ℝ) :=
  eventually_scaled_inv_deriv_window_at_zero_of_variation
    (c := c) (ζ := ζ) (z := z) (α := α) (n := n)
    (R := R) (r := r) (μ := μ) (K := K)
    hhit hfix hinit hrep hr hμ hK hcenter_margin hsmall_margin
    (eventually_inverse_scaled_closedBall_subset_ball_of_repelling_hit
      hhit hfix hinit hrep hz hr)
    hvar

/-- Selector bridge for the inverse-multiplier scaled window centered at `0`, with geometric
containment automatic.  The remaining local input is only the scaled derivative-variation estimate,
plus explicit real margins for the chosen scaled radius. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_only_half_not_postcritical
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
          ∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall (0 : ℂ) r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_inv_deriv_window_half
    hαfix hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨r, μ, K, hr, hμ, hK, hcenter, hsmall, hvar⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
    (orbitProduct_ne_zero_iff_no_precritical c z n).2
      (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit)
  exact eventually_scaled_inv_deriv_window_at_zero_of_variation_auto_containment
    (c := c) (ζ := z₀) (z := z) (α := α) (n := n)
    (R := R) (r := r) (μ := μ) (K := K)
    hhit hαfix hinit hαrep hz hr hμ hK hcenter hsmall hvar

/-- Selector bridge where the local input is an unscaled derivative-variation bound on the
shrinking physical inverse-multiplier ball. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_physical_variation_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal) (M : ℕ → ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
          (2 : ℝ) * μ ≤ (K : ℝ) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ w ∈ Metric.closedBall z
                (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
              ‖deriv ((quadratic c)^[n + m]) w -
                deriv ((quadratic c)^[n + m]) z‖ ≤ M m) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * M m ≤ μ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_only_half_not_postcritical
    hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨r, μ, K, M, hr, hμ, hK, hcenter, hsmall, hphys, hscale⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  refine ⟨r, μ, K, hr, hμ, hK, hcenter, hsmall, ?_⟩
  exact eventually_scaled_deriv_variation_of_physical_deriv_variation
    (c := c) (z := z) (n := n) (r := r) (μ := μ) M hphys hscale

/-- Selector bridge where the local input is a second-derivative bound on the shrinking physical
inverse-multiplier ball. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_second_deriv_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal) (B : ℕ → ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
          (2 : ℝ) * μ ≤ (K : ℝ) ∧
          (∀ᶠ m : ℕ in atTop, 0 ≤ B m) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ y ∈ Metric.closedBall z
                (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B m) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
              (B m * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_only_half_not_postcritical
    hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨r, μ, K, B, hr, hμ, hK, hcenter, hsmall, hB, hsecond, hscale⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  refine ⟨r, μ, K, hr, hμ, hK, hcenter, hsmall, ?_⟩
  exact eventually_scaled_deriv_variation_of_second_deriv_bound
    (c := c) (z := z) (n := n) (r := r) (μ := μ) B hr hB hsecond hscale

/-- Selector bridge where the local second-derivative bound is chosen tail-by-tail. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_eventual_second_deriv_half_not_postcritical
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
          ∀ᶠ m : ℕ in atTop,
            ∃ B : ℝ, 0 ≤ B ∧
              (∀ y ∈ Metric.closedBall z
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_only_half_not_postcritical
    hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨r, μ, K, hr, hμ, hK, hcenter, hsmall, hsecond⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  refine ⟨r, μ, K, hr, hμ, hK, hcenter, hsmall, ?_⟩
  exact eventually_scaled_deriv_variation_of_eventual_second_deriv_bound
    (c := c) (z := z) (n := n) (r := r) (μ := μ) hr hsecond

/-- Concrete-parameter selector bridge.  The Newton parameters are fixed to
`K = 1/2`, `μ = 1/4`, and scaled radius `4‖α-z‖`; the only remaining local input is the
tail-by-tail second-derivative smallness estimate at that radius. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_explicit_second_deriv_quarter_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ B : ℝ, 0 ≤ B ∧
            (∀ y ∈ Metric.closedBall z
                (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                  ((4 : ℝ) * ‖α - z‖)),
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
              (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                ((4 : ℝ) * ‖α - z‖))) ≤ (1 / 4 : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_eventual_second_deriv_half_not_postcritical
    hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  refine ⟨(4 : ℝ) * ‖α - z‖, (1 / 4 : ℝ), (1 / 2 : NNReal), ?_, by norm_num,
    by norm_num, ?_, by norm_num, ?_⟩
  · exact mul_nonneg (by norm_num) (norm_nonneg _)
  · have hcoef : (1 - ((1 / 2 : NNReal) : ℝ)) = (1 / 2 : ℝ) := by norm_num
    rw [hcoef]
    nlinarith [norm_nonneg (α - z)]
  · exact hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit

/-- q62 target-density reduction from the scaled-at-zero variation-only local input. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_at_zero_variation_only_half_not_postcritical_eventually_nonStrong_subset
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
          ∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall (0 : ℂ) r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) 0‖ ≤ μ)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_variation_only_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

/-- q62 target-density reduction from the physical derivative-variation local input. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_at_zero_physical_variation_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal) (M : ℕ → ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
          (2 : ℝ) * μ ≤ (K : ℝ) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ w ∈ Metric.closedBall z
                (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
              ‖deriv ((quadratic c)^[n + m]) w -
                deriv ((quadratic c)^[n + m]) z‖ ≤ M m) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * M m ≤ μ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_physical_variation_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

/-- q62 target-density reduction from the second-derivative local input on shrinking physical balls. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_at_zero_second_deriv_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (r μ : ℝ) (K : NNReal) (B : ℕ → ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (2 : ℝ) * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
          (2 : ℝ) * μ ≤ (K : ℝ) ∧
          (∀ᶠ m : ℕ in atTop, 0 ≤ B m) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ y ∈ Metric.closedBall z
                (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B m) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
              (B m * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_second_deriv_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

/-- q62 target-density reduction from tail-by-tail second-derivative windows on shrinking physical
balls. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_at_zero_eventual_second_deriv_half_not_postcritical_eventually_nonStrong_subset
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
          ∀ᶠ m : ℕ in atTop,
            ∃ B : ℝ, 0 ≤ B ∧
              (∀ y ∈ Metric.closedBall z
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ)
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_eventual_second_deriv_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

/-- q62 target-density reduction with concrete Newton parameters.  The remaining hRigid local
obligation is exactly the eventual second-derivative smallness estimate at scaled radius
`4‖α-z‖`. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_at_zero_explicit_second_deriv_quarter_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ B : ℝ, 0 ≤ B ∧
            (∀ y ∈ Metric.closedBall z
                (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                  ((4 : ℝ) * ‖α - z‖)),
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
              (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                ((4 : ℝ) * ‖α - z‖))) ≤ (1 / 4 : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_at_zero_explicit_second_deriv_quarter_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

end

end Bottcher
