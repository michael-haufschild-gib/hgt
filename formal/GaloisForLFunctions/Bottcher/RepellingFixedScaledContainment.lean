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

/-- Arbitrary-center version of
`eventually_inverse_scaled_closedBall_subset_ball_of_repelling_hit`.

For any fixed scaled center `τ` and radius `r`, inverse-multiplier scaled closed balls
`closedBall τ r` shrink back into the requested target ball. -/
theorem eventually_inverse_scaled_closedBall_subset_ball_of_repelling_hit_center
    {c ζ z α τ : ℂ} {n : ℕ} {R r : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hz : z ∈ Metric.ball ζ (R / 2)) (hr : 0 ≤ r) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall τ r,
        z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t ∈ Metric.ball ζ R := by
  rw [Metric.mem_ball] at hz
  have hRhalf : 0 < R / 2 := lt_of_le_of_lt dist_nonneg hz
  let C : ℝ := ‖τ‖ + r + 1
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith [norm_nonneg τ, hr]
  let ε : ℝ := (R / 2) / C
  have hε : 0 < ε := div_pos hRhalf hCpos
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
  have ht_dist : dist t τ ≤ r := by
    simpa [Metric.mem_closedBall] using ht
  have ht_norm : ‖t‖ ≤ ‖τ‖ + r := by
    calc
      ‖t‖ = ‖(t - τ) + τ‖ := by ring_nf
      _ ≤ ‖t - τ‖ + ‖τ‖ := norm_add_le _ _
      _ = dist t τ + ‖τ‖ := by rw [dist_eq_norm]
      _ ≤ r + ‖τ‖ := by linarith
      _ = ‖τ‖ + r := by ring
  have hstep_le : dist (z + D⁻¹ * t) z ≤ R / 2 := by
    have hmul : ‖D⁻¹ * t‖ ≤ ε * (‖τ‖ + r) := by
      rw [norm_mul]
      exact mul_le_mul (le_of_lt hinvlt) ht_norm (norm_nonneg _) (le_of_lt hε)
    have hεC : ε * (‖τ‖ + r) ≤ R / 2 := by
      have hleC : ‖τ‖ + r ≤ C := by
        dsimp [C]
        linarith
      calc
        ε * (‖τ‖ + r) ≤ ε * C := mul_le_mul_of_nonneg_left hleC (le_of_lt hε)
        _ = R / 2 := by
          dsimp [ε]
          rw [div_mul_cancel₀ _ (ne_of_gt hCpos)]
    calc
      dist (z + D⁻¹ * t) z = ‖D⁻¹ * t‖ := by
        rw [dist_eq_norm]
        congr 1
        ring
      _ ≤ ε * (‖τ‖ + r) := hmul
      _ ≤ R / 2 := hεC
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

/-- Arbitrary-center version of
`scaled_deriv_variation_le_of_physical_deriv_variation`.

The physical derivative-variation ball is centered at the physical point corresponding to the
scaled center `τ`. -/
theorem scaled_deriv_variation_le_of_physical_deriv_variation_center
    {c z τ : ℂ} {q : ℕ} {r M μ : ℝ}
    (hphys : ∀ w ∈ Metric.closedBall
        (z + (deriv ((quadratic c)^[q]) z)⁻¹ * τ)
        (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r),
      ‖deriv ((quadratic c)^[q]) w -
        deriv ((quadratic c)^[q]) (z + (deriv ((quadratic c)^[q]) z)⁻¹ * τ)‖ ≤ M)
    (hsmall : ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * M ≤ μ) :
    ∀ t ∈ Metric.closedBall τ r,
      ‖deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) t -
        deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) τ‖ ≤ μ := by
  intro t ht
  let D : ℂ := deriv ((quadratic c)^[q]) z
  let wτ : ℂ := z + D⁻¹ * τ
  let w : ℂ := z + D⁻¹ * t
  have ht_dist : dist t τ ≤ r := by
    simpa [Metric.mem_closedBall] using ht
  have hw : w ∈ Metric.closedBall wτ (‖D⁻¹‖ * r) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hmul : ‖D⁻¹ * (t - τ)‖ ≤ ‖D⁻¹‖ * r := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using ht_dist) (norm_nonneg _)
    calc
      ‖w - wτ‖ = ‖D⁻¹ * (t - τ)‖ := by
        dsimp [w, wτ]
        congr 1
        ring
      _ ≤ ‖D⁻¹‖ * r := hmul
  have hdt :
      deriv
          (fun u => (quadratic c)^[q] (z + D⁻¹ * u) - (z + D⁻¹ * u)) t =
        D⁻¹ * (deriv ((quadratic c)^[q]) w - 1) := by
    dsimp [w, D]
    exact deriv_scaled_displacement c z ((deriv ((quadratic c)^[q]) z)⁻¹) t q
  have hdτ :
      deriv
          (fun u => (quadratic c)^[q] (z + D⁻¹ * u) - (z + D⁻¹ * u)) τ =
        D⁻¹ * (deriv ((quadratic c)^[q]) wτ - 1) := by
    dsimp [wτ, D]
    exact deriv_scaled_displacement c z ((deriv ((quadratic c)^[q]) z)⁻¹) τ q
  dsimp [D] at hdt hdτ
  rw [hdt, hdτ]
  have hdiff :
      (deriv ((quadratic c)^[q]) z)⁻¹ *
          (deriv ((quadratic c)^[q]) w - 1) -
        (deriv ((quadratic c)^[q]) z)⁻¹ *
          (deriv ((quadratic c)^[q]) wτ - 1) =
        (deriv ((quadratic c)^[q]) z)⁻¹ *
          (deriv ((quadratic c)^[q]) w - deriv ((quadratic c)^[q]) wτ) := by
    ring
  rw [hdiff, norm_mul]
  exact le_trans
    (mul_le_mul_of_nonneg_left
      (hphys w (by simpa [D, w, wτ] using hw)) (norm_nonneg _))
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

/-- Arbitrary-center second-derivative version of
`scaled_deriv_variation_le_of_second_deriv_bound`. -/
theorem scaled_deriv_variation_le_of_second_deriv_bound_center
    {c z τ : ℂ} {q : ℕ} {r B μ : ℝ}
    (hr : 0 ≤ r)
    (hB : 0 ≤ B)
    (hsecond : ∀ y ∈ Metric.closedBall
        (z + (deriv ((quadratic c)^[q]) z)⁻¹ * τ)
        (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r),
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ B)
    (hsmall :
      ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ *
        (B * (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ t ∈ Metric.closedBall τ r,
      ‖deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) t -
        deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) τ‖ ≤ μ := by
  let ρ : ℝ := ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact mul_nonneg (norm_nonneg _) hr
  have hphys :
      ∀ y ∈ Metric.closedBall (z + (deriv ((quadratic c)^[q]) z)⁻¹ * τ) ρ,
        ‖deriv ((quadratic c)^[q]) y -
          deriv ((quadratic c)^[q]) (z + (deriv ((quadratic c)^[q]) z)⁻¹ * τ)‖ ≤
            B * ρ :=
    deriv_variation_quadratic_iterate_le_of_second_deriv_bound_closedBall
      (c := c) (z := z + (deriv ((quadratic c)^[q]) z)⁻¹ * τ)
      (q := q) (r := ρ) (M := B) hρ hB (by
        simpa [ρ] using hsecond)
  exact scaled_deriv_variation_le_of_physical_deriv_variation_center
    (c := c) (z := z) (τ := τ) (q := q) (r := r) (M := B * ρ) (μ := μ)
    (by simpa [ρ] using hphys) (by simpa [ρ] using hsmall)

/-- A scaled closed ball around an arbitrary fixed scaled center is contained in the base-centered
scaled closed ball whose radius is enlarged by `‖τ‖`. -/
theorem inverse_scaled_center_closedBall_subset_base_closedBall
    {z D τ : ℂ} {r : ℝ} :
    Metric.closedBall (z + D⁻¹ * τ) (‖D⁻¹‖ * r) ⊆
      Metric.closedBall z (‖D⁻¹‖ * (‖τ‖ + r)) := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  have hcenter : dist (z + D⁻¹ * τ) z = ‖D⁻¹ * τ‖ := by
    rw [dist_eq_norm]
    congr 1
    ring
  calc
    dist y z ≤ dist y (z + D⁻¹ * τ) + dist (z + D⁻¹ * τ) z := dist_triangle _ _ _
    _ ≤ ‖D⁻¹‖ * r + ‖D⁻¹ * τ‖ := by
      rw [hcenter]
      exact add_le_add hy le_rfl
    _ = ‖D⁻¹‖ * (‖τ‖ + r) := by
      rw [norm_mul]
      ring

/-- Arbitrary-center second-derivative transfer from a base-centered shrinking physical ball.

This replaces a moving physical ball centered at `z + D⁻¹τ` by the single base-centered ball with
scaled radius `‖τ‖ + r`. -/
theorem scaled_deriv_variation_le_of_second_deriv_bound_center_base
    {c z τ : ℂ} {q : ℕ} {r B μ : ℝ}
    (hr : 0 ≤ r)
    (hB : 0 ≤ B)
    (hsecond : ∀ y ∈ Metric.closedBall z
        (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * (‖τ‖ + r)),
      ‖deriv (fun w => deriv ((quadratic c)^[q]) w) y‖ ≤ B)
    (hsmall :
      ‖(deriv ((quadratic c)^[q]) z)⁻¹‖ *
        (B * (‖(deriv ((quadratic c)^[q]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ t ∈ Metric.closedBall τ r,
      ‖deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) t -
        deriv
          (fun u => (quadratic c)^[q]
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u) -
            (z + (deriv ((quadratic c)^[q]) z)⁻¹ * u)) τ‖ ≤ μ := by
  refine scaled_deriv_variation_le_of_second_deriv_bound_center
    (c := c) (z := z) (τ := τ) (q := q) (r := r) (B := B) (μ := μ)
    hr hB ?_ hsmall
  intro y hy
  exact hsecond y (inverse_scaled_center_closedBall_subset_base_closedBall
    (z := z) (D := deriv ((quadratic c)^[q]) z) (τ := τ) hy)

/-- Eventual existential arbitrary-center form of
`scaled_deriv_variation_le_of_second_deriv_bound_center`. -/
theorem eventually_scaled_deriv_variation_of_eventual_second_deriv_bound_center
    {c z τ : ℂ} {n : ℕ} {r μ : ℝ}
    (hr : 0 ≤ r)
    (hsecond : ∀ᶠ m : ℕ in atTop,
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ y ∈ Metric.closedBall
            (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall τ r,
        ‖deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
          deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) τ‖ ≤ μ := by
  filter_upwards [hsecond] with m hm
  rcases hm with ⟨B, hB, hbound, hsmall⟩
  exact scaled_deriv_variation_le_of_second_deriv_bound_center
    (c := c) (z := z) (τ := τ) (q := n + m) (r := r) (B := B) (μ := μ)
    hr hB hbound hsmall

/-- Eventual base-centered version of
`scaled_deriv_variation_le_of_second_deriv_bound_center_base`. -/
theorem eventually_scaled_deriv_variation_of_eventual_second_deriv_bound_center_base
    {c z τ : ℂ} {n : ℕ} {r μ : ℝ}
    (hr : 0 ≤ r)
    (hsecond : ∀ᶠ m : ℕ in atTop,
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r)),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ t ∈ Metric.closedBall τ r,
        ‖deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
          deriv
            (fun u => (quadratic c)^[n + m]
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
              (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) τ‖ ≤ μ := by
  filter_upwards [hsecond] with m hm
  rcases hm with ⟨B, hB, hbound, hsmall⟩
  exact scaled_deriv_variation_le_of_second_deriv_bound_center_base
    (c := c) (z := z) (τ := τ) (q := n + m) (r := r) (B := B) (μ := μ)
    hr hB hbound hsmall

/-- Scalar fixed-tail estimate for the normalized second-derivative term at the pre-hit base point.

The exact fixed-tail second-derivative decomposition has a leading term of size
`C * ‖2α‖^(2m) * ‖(f^[n])' z‖^(2 : ℕ)` and a lower-order term of size `‖2α‖^m`.  After the two
inverse-multiplier normalizations in the scaled Newton window, the leading term contributes
`C * r` and the lower-order term tends to zero. -/
theorem eventually_scaled_base_second_deriv_term_le_of_repelling_hit
    {c z α : ℂ} {n : ℕ} {C r μ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hCnonneg : 0 ≤ C)
    (hC : 2 ≤ C * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hr : 0 ≤ r)
    (hCr : C * r < μ) :
    ∀ᶠ m : ℕ in atTop,
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
        (‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) z‖ *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  let P : ℝ := ‖deriv ((quadratic c)^[n]) z‖
  let L : ℝ := ‖(2 : ℂ) * α‖
  let B : ℝ := ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖
  have hPpos : 0 < P := by
    dsimp [P]
    rw [deriv_quadratic_iterate_eq_orbitProduct_core]
    exact norm_pos_iff.mpr hinit
  have hPne : P ≠ 0 := ne_of_gt hPpos
  have hLgt : 1 < L := by simpa [L] using hrep
  have hLpos : 0 < L := lt_trans zero_lt_one hLgt
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hdecay : Tendsto (fun m : ℕ => (B * r) * ((P ^ 2 * L ^ m)⁻¹)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun m : ℕ => L ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hLgt
    have hP2pos : 0 < P ^ 2 := sq_pos_of_pos hPpos
    have hmul_atTop : Tendsto (fun m : ℕ => P ^ 2 * L ^ m) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hP2pos hpow
    have hinv : Tendsto (fun m : ℕ => (P ^ 2 * L ^ m)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hmul_atTop
    simpa using hinv.const_mul (B * r)
  have hmajor_tendsto :
      Tendsto (fun m : ℕ => C * r + (B * r) * ((P ^ 2 * L ^ m)⁻¹)) atTop
        (𝓝 (C * r)) := by
    simpa using tendsto_const_nhds.add hdecay
  have hmajor_lt : ∀ᶠ m : ℕ in atTop,
      C * r + (B * r) * ((P ^ 2 * L ^ m)⁻¹) < μ :=
    (tendsto_order.1 hmajor_tendsto).2 μ hCr
  filter_upwards [hmajor_lt] with m hlt
  have hDnorm : ‖deriv ((quadratic c)^[n + m]) z‖ = P * L ^ m := by
    dsimp [P, L]
    rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m, norm_mul, norm_pow]
    rw [deriv_quadratic_iterate_eq_orbitProduct_core]
  have hDinvnorm : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ = (P * L ^ m)⁻¹ := by
    rw [norm_inv, hDnorm]
  have hsecond_le := norm_deriv_deriv_fixed_tail_of_iterate_eq_fixed_le
    (c := c) (z := z) (α := α) (n := n) (C := C)
    hhit hfix hCnonneg hC m
  have hnonneg_inner : 0 ≤ ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r :=
    mul_nonneg (norm_nonneg _) hr
  calc
    ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
        (‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) z‖ *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r))
        ≤ ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          ((C * L ^ (2 * m) * P ^ 2 + L ^ m * B) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) := by
          dsimp [P, L, B] at hsecond_le ⊢
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsecond_le hnonneg_inner) (norm_nonneg _)
    _ = (P * L ^ m)⁻¹ * ((C * L ^ (2 * m) * P ^ 2 + L ^ m * B) *
          ((P * L ^ m)⁻¹ * r)) := by rw [hDinvnorm]
    _ = C * r + (B * r) * ((P ^ 2 * L ^ m)⁻¹) := by
          field_simp [hPne, hLne]
          ring_nf
    _ ≤ μ := le_of_lt hlt

/-- Explicit-constant version of
`eventually_scaled_base_second_deriv_term_le_of_repelling_hit`.

The leading fixed-tail second-derivative coefficient may be bounded with
`C = 2 / (‖2α‖ * (‖2α‖ - 1))`; hence the scalar smallness condition is exactly that
constant times the scaled radius is below `μ`. -/
theorem eventually_scaled_base_second_deriv_term_le_of_repelling_hit_explicit
    {c z α : ℂ} {n : ℕ} {r μ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hr : 0 ≤ r)
    (hsmall : ((2 : ℝ) / (‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))) * r < μ) :
    ∀ᶠ m : ℕ in atTop,
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
        (‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) z‖ *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  let L : ℝ := ‖(2 : ℂ) * α‖
  let C : ℝ := (2 : ℝ) / (L * (L - 1))
  have hLgt : 1 < L := by simpa [L] using hrep
  have hLpos : 0 < L := lt_trans zero_lt_one hLgt
  have hLm1pos : 0 < L - 1 := by linarith
  have hdenpos : 0 < L * (L - 1) := mul_pos hLpos hLm1pos
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (by norm_num) (le_of_lt hdenpos)
  have hCbound : 2 ≤ C * L * (L - 1) := by
    dsimp [C]
    field_simp [ne_of_gt hdenpos]
    norm_num
  have hCr : C * r < μ := by simpa [C, L] using hsmall
  exact eventually_scaled_base_second_deriv_term_le_of_repelling_hit
    (c := c) (z := z) (α := α) (n := n) (C := C) (r := r) (μ := μ)
    hhit hfix hinit hrep hCnonneg hCbound hr hCr

/-- Scalar fixed-tail estimate for the normalized third-derivative term at the pre-hit base point.

After the three inverse-multiplier normalizations in the third-derivative excess window, the leading
third-derivative tail coefficient contributes `C₃ * ρ * r`; the lower-order chain-rule terms decay
along the repelling fixed tail. -/
theorem eventually_scaled_base_third_deriv_term_le_of_repelling_hit
    {c z α : ℂ} {n : ℕ} {C₂ C₃ ρ r μ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hC₂nonneg : 0 ≤ C₂)
    (hC₂ : 2 ≤ C₂ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 2 - 1))
    (hρ : 0 ≤ ρ)
    (hr : 0 ≤ r)
    (hsmall : C₃ * ρ * r < μ) :
    ∀ᶠ m : ℕ in atTop,
      ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
        ((‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z‖ *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  let P : ℝ := ‖deriv ((quadratic c)^[n]) z‖
  let L : ℝ := ‖(2 : ℂ) * α‖
  let B : ℝ := ‖deriv (fun w => deriv ((quadratic c)^[n]) w) z‖
  let C : ℝ := ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n]) v) w) z‖
  have hPpos : 0 < P := by
    dsimp [P]
    rw [deriv_quadratic_iterate_eq_orbitProduct_core]
    exact norm_pos_iff.mpr hinit
  have hPne : P ≠ 0 := ne_of_gt hPpos
  have hLgt : 1 < L := by simpa [L] using hrep
  have hLpos : 0 < L := lt_trans zero_lt_one hLgt
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hpow : Tendsto (fun m : ℕ => L ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hLgt
  have hP2pos : 0 < P ^ 2 := sq_pos_of_pos hPpos
  have hden1 : Tendsto (fun m : ℕ => P ^ 2 * L ^ m) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hP2pos hpow
  have hdecay1 : Tendsto
      (fun m : ℕ => (3 * C₂ * B * ρ * r) * ((P ^ 2 * L ^ m)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hden1).const_mul (3 * C₂ * B * ρ * r)
  have hL2gt : 1 < L ^ 2 := by nlinarith
  have hpow2base : Tendsto (fun m : ℕ => (L ^ 2) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hL2gt
  have hpow2 : Tendsto (fun m : ℕ => L ^ (2 * m)) atTop atTop := by
    refine hpow2base.congr' ?_
    filter_upwards with m
    rw [pow_mul]
  have hP3pos : 0 < P ^ 3 := by positivity
  have hden2 : Tendsto (fun m : ℕ => P ^ 3 * L ^ (2 * m)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hP3pos hpow2
  have hdecay2 : Tendsto
      (fun m : ℕ => (C * ρ * r) * ((P ^ 3 * L ^ (2 * m))⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hden2).const_mul (C * ρ * r)
  have hmajor_tendsto :
      Tendsto
        (fun m : ℕ =>
          C₃ * ρ * r +
            (3 * C₂ * B * ρ * r) * ((P ^ 2 * L ^ m)⁻¹) +
            (C * ρ * r) * ((P ^ 3 * L ^ (2 * m))⁻¹)) atTop
        (𝓝 (C₃ * ρ * r)) := by
    simpa [add_assoc] using (tendsto_const_nhds.add hdecay1).add hdecay2
  have hmajor_lt : ∀ᶠ m : ℕ in atTop,
      C₃ * ρ * r +
          (3 * C₂ * B * ρ * r) * ((P ^ 2 * L ^ m)⁻¹) +
          (C * ρ * r) * ((P ^ 3 * L ^ (2 * m))⁻¹) < μ :=
    (tendsto_order.1 hmajor_tendsto).2 μ hsmall
  filter_upwards [hmajor_lt] with m hlt
  have hDnorm : ‖deriv ((quadratic c)^[n + m]) z‖ = P * L ^ m := by
    dsimp [P, L]
    rw [deriv_fixed_tail_of_iterate_eq_fixed hhit hfix m, norm_mul, norm_pow]
    rw [deriv_quadratic_iterate_eq_orbitProduct_core]
  have hDinvnorm : ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ = (P * L ^ m)⁻¹ := by
    rw [norm_inv, hDnorm]
  have hthird_le := norm_deriv_deriv_deriv_fixed_tail_of_iterate_eq_fixed_le
    (c := c) (z := z) (α := α) (n := n) (C₂ := C₂) (C₃ := C₃)
    hhit hfix hrep hC₂nonneg hC₂ hC₃nonneg hC₃ m
  have hnonneg_inner :
      0 ≤ (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ) := by
    exact mul_nonneg (norm_nonneg _) hρ
  have hnonneg_inner_r :
      0 ≤ ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r := by
    exact mul_nonneg (norm_nonneg _) hr
  calc
    ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
        ((‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z‖ *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
          (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r))
        ≤ ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (((C₃ * L ^ (3 * m) * P ^ 3 +
              3 * C₂ * L ^ (2 * m) * P * B +
              L ^ m * C) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) := by
          dsimp [P, L, B, C] at hthird_le ⊢
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hthird_le hnonneg_inner)
              hnonneg_inner_r)
            (norm_nonneg _)
    _ = (P * L ^ m)⁻¹ *
          (((C₃ * L ^ (3 * m) * P ^ 3 +
              3 * C₂ * L ^ (2 * m) * P * B +
              L ^ m * C) *
            ((P * L ^ m)⁻¹ * ρ)) *
            ((P * L ^ m)⁻¹ * r)) := by rw [hDinvnorm]
    _ = C₃ * ρ * r +
          (3 * C₂ * B * ρ * r) * ((P ^ 2 * L ^ m)⁻¹) +
          (C * ρ * r) * ((P ^ 3 * L ^ (2 * m))⁻¹) := by
          field_simp [hPne, hLne]
          ring_nf
    _ ≤ μ := le_of_lt hlt

/-- Combine a basepoint third-derivative contribution with a local third-derivative excess
estimate on the shrinking ball.

This is the third-derivative analogue of `eventually_second_deriv_bound_of_base_and_excess`: once
the basepoint term and the local oscillation term are separately small after the three
inverse-multiplier normalizations, their sum gives the full third-derivative window. -/
theorem eventually_third_deriv_bound_of_base_and_excess
    {D : ℕ → ℂ} {H : ℕ → ℂ → ℂ} {z : ℂ} {ρ r μ₀ μ₁ μ : ℝ}
    (hbase : ∀ᶠ m : ℕ in atTop,
      ‖(D m)⁻¹‖ * ((‖H m z‖ * (‖(D m)⁻¹‖ * ρ)) *
        (‖(D m)⁻¹‖ * r)) ≤ μ₀)
    (hexcess : ∀ᶠ m : ℕ in atTop,
      ∃ E : ℝ, 0 ≤ E ∧
        (∀ y ∈ Metric.closedBall z (‖(D m)⁻¹‖ * ρ), ‖H m y - H m z‖ ≤ E) ∧
        ‖(D m)⁻¹‖ * ((E * (‖(D m)⁻¹‖ * ρ)) *
          (‖(D m)⁻¹‖ * r)) ≤ μ₁)
    (hsum : μ₀ + μ₁ ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ T : ℝ, 0 ≤ T ∧
        (∀ y ∈ Metric.closedBall z (‖(D m)⁻¹‖ * ρ), ‖H m y‖ ≤ T) ∧
        ‖(D m)⁻¹‖ * ((T * (‖(D m)⁻¹‖ * ρ)) *
          (‖(D m)⁻¹‖ * r)) ≤ μ := by
  filter_upwards [hbase, hexcess] with m hbase_m hexcess_m
  rcases hexcess_m with ⟨E, hE, hEbound, hEsmall⟩
  refine ⟨‖H m z‖ + E, add_nonneg (norm_nonneg _) hE, ?_, ?_⟩
  · intro y hy
    calc
      ‖H m y‖ = ‖H m z + (H m y - H m z)‖ := by
        congr 1
        ring
      _ ≤ ‖H m z‖ + ‖H m y - H m z‖ := norm_add_le _ _
      _ ≤ ‖H m z‖ + E := by
        simpa [add_comm] using add_le_add_right (hEbound y hy) ‖H m z‖
  · calc
      ‖(D m)⁻¹‖ * (((‖H m z‖ + E) * (‖(D m)⁻¹‖ * ρ)) *
          (‖(D m)⁻¹‖ * r))
          = ‖(D m)⁻¹‖ * ((‖H m z‖ * (‖(D m)⁻¹‖ * ρ)) *
              (‖(D m)⁻¹‖ * r)) +
            ‖(D m)⁻¹‖ * ((E * (‖(D m)⁻¹‖ * ρ)) *
              (‖(D m)⁻¹‖ * r)) := by
            ring
      _ ≤ μ₀ + μ₁ := add_le_add hbase_m hEsmall
      _ ≤ μ := hsum

/-- Fixed-tail third-derivative window from a local excess estimate.

The basepoint third-derivative contribution is discharged by
`eventually_scaled_base_third_deriv_term_le_of_repelling_hit`; the remaining analytic input is only
the oscillation of the third-derivative function on the shrinking base-centered ball. -/
theorem eventually_base_center_third_deriv_bound_of_repelling_hit_excess
    {c z α : ℂ} {n : ℕ} {C₂ C₃ ρ r μ₀ μ₁ μ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hC₂nonneg : 0 ≤ C₂)
    (hC₂ : 2 ≤ C₂ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hC₃nonneg : 0 ≤ C₃)
    (hC₃ : 6 * C₂ ≤ C₃ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 2 - 1))
    (hρ : 0 ≤ ρ)
    (hr : 0 ≤ r)
    (hC₃ρr : C₃ * ρ * r < μ₀)
    (hexcess : ∀ᶠ m : ℕ in atTop,
      ∃ E : ℝ, 0 ≤ E ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y -
            deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z‖ ≤ E) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          ((E * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ₁)
    (hsum : μ₀ + μ₁ ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ T : ℝ, 0 ≤ T ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y‖ ≤ T) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          ((T * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  refine eventually_third_deriv_bound_of_base_and_excess
    (D := fun m => deriv ((quadratic c)^[n + m]) z)
    (H := fun m y => deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y)
    (z := z) (ρ := ρ) (r := r) (μ₀ := μ₀) (μ₁ := μ₁) (μ := μ) ?_ hexcess hsum
  exact eventually_scaled_base_third_deriv_term_le_of_repelling_hit
    (c := c) (z := z) (α := α) (n := n) (C₂ := C₂) (C₃ := C₃)
    (ρ := ρ) (r := r) (μ := μ₀)
    hhit hfix hinit hrep hC₂nonneg hC₂ hC₃nonneg hC₃ hρ hr hC₃ρr

/-- Combine a basepoint second-derivative contribution with a local excess estimate.

This is the algebraic step behind the remaining uniform fixed-tail window: once the basepoint term
and the local oscillation term are separately small after the two inverse-multiplier normalizations,
their sum gives the required bound on the whole shrinking ball. -/
theorem eventually_second_deriv_bound_of_base_and_excess
    {D : ℕ → ℂ} {H : ℕ → ℂ → ℂ} {z : ℂ} {ρ r μ₀ μ₁ μ : ℝ}
    (hbase : ∀ᶠ m : ℕ in atTop,
      ‖(D m)⁻¹‖ * (‖H m z‖ * (‖(D m)⁻¹‖ * r)) ≤ μ₀)
    (hexcess : ∀ᶠ m : ℕ in atTop,
      ∃ E : ℝ, 0 ≤ E ∧
        (∀ y ∈ Metric.closedBall z (‖(D m)⁻¹‖ * ρ), ‖H m y - H m z‖ ≤ E) ∧
        ‖(D m)⁻¹‖ * (E * (‖(D m)⁻¹‖ * r)) ≤ μ₁)
    (hsum : μ₀ + μ₁ ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ y ∈ Metric.closedBall z (‖(D m)⁻¹‖ * ρ), ‖H m y‖ ≤ B) ∧
        ‖(D m)⁻¹‖ * (B * (‖(D m)⁻¹‖ * r)) ≤ μ := by
  filter_upwards [hbase, hexcess] with m hbase_m hexcess_m
  rcases hexcess_m with ⟨E, hE, hEbound, hEsmall⟩
  refine ⟨‖H m z‖ + E, add_nonneg (norm_nonneg _) hE, ?_, ?_⟩
  · intro y hy
    calc
      ‖H m y‖ = ‖H m z + (H m y - H m z)‖ := by
        congr 1
        ring
      _ ≤ ‖H m z‖ + ‖H m y - H m z‖ := norm_add_le _ _
      _ ≤ ‖H m z‖ + E := by
        simpa [add_comm] using add_le_add_right (hEbound y hy) ‖H m z‖
  · calc
      ‖(D m)⁻¹‖ * ((‖H m z‖ + E) * (‖(D m)⁻¹‖ * r))
          = ‖(D m)⁻¹‖ * (‖H m z‖ * (‖(D m)⁻¹‖ * r)) +
              ‖(D m)⁻¹‖ * (E * (‖(D m)⁻¹‖ * r)) := by
            ring
      _ ≤ μ₀ + μ₁ := add_le_add hbase_m hEsmall
      _ ≤ μ := hsum

/-- Fixed-tail version of `eventually_second_deriv_bound_of_base_and_excess`.

The basepoint part is discharged by the fixed-tail scalar estimate; the only remaining analytic
input is a local excess estimate for
`deriv (fun w => deriv ((quadratic c)^[n+m]) w)` on the shrinking base-centered ball. -/
theorem eventually_base_center_second_deriv_bound_of_repelling_hit_excess
    {c z α : ℂ} {n : ℕ} {C ρ r μ₀ μ₁ μ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hCnonneg : 0 ≤ C)
    (hC : 2 ≤ C * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hr : 0 ≤ r)
    (hCr : C * r < μ₀)
    (hexcess : ∀ᶠ m : ℕ in atTop,
      ∃ E : ℝ, 0 ≤ E ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y -
            deriv (fun w => deriv ((quadratic c)^[n + m]) w) z‖ ≤ E) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (E * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ₁)
    (hsum : μ₀ + μ₁ ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  refine eventually_second_deriv_bound_of_base_and_excess
    (D := fun m => deriv ((quadratic c)^[n + m]) z)
    (H := fun m y => deriv (fun w => deriv ((quadratic c)^[n + m]) w) y)
    (z := z) (ρ := ρ) (r := r) (μ₀ := μ₀) (μ₁ := μ₁) (μ := μ) ?_ hexcess hsum
  exact eventually_scaled_base_second_deriv_term_le_of_repelling_hit
    (c := c) (z := z) (α := α) (n := n) (C := C) (r := r) (μ := μ₀)
    hhit hfix hinit hrep hCnonneg hC hr hCr

/-- A third-derivative bound gives the local excess estimate for the second-derivative function on
the same shrinking ball. -/
theorem eventually_second_deriv_excess_of_third_deriv_bound
    {c z : ℂ} {n : ℕ} {ρ r μ : ℝ}
    (hρ : 0 ≤ ρ)
    (hthird : ∀ᶠ m : ℕ in atTop,
      ∃ T : ℝ, 0 ≤ T ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y‖ ≤ T) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          ((T * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ E : ℝ, 0 ≤ E ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y -
            deriv (fun w => deriv ((quadratic c)^[n + m]) w) z‖ ≤ E) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (E * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  filter_upwards [hthird] with m hm
  rcases hm with ⟨T, hT, hbound, hsmall⟩
  let rad : ℝ := ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ
  have hrad : 0 ≤ rad := by
    dsimp [rad]
    exact mul_nonneg (norm_nonneg _) hρ
  refine ⟨T * rad, mul_nonneg hT hrad, ?_, ?_⟩
  · exact deriv_variation_le_of_deriv_bound_closedBall
      (G := fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w)
      (z := z) (r := rad) (M := T) hrad hT
      (fun y _hy => (((analyticAt_quadratic_iterate c (n + m) y).deriv).deriv.differentiableAt))
      (by simpa [rad] using hbound)
  · simpa [rad] using hsmall

/-- A fourth-derivative bound gives the local excess estimate for the third-derivative function on
the same shrinking ball.

This is the first non-opaque form of the remaining third-derivative excess obligation: it turns the
oscillation of the third derivative into a fourth-derivative bound with the correct inverse-multiplier
normalization. -/
theorem eventually_third_deriv_excess_of_fourth_deriv_bound
    {c z : ℂ} {n : ℕ} {ρ r μ : ℝ}
    (hρ : 0 ≤ ρ)
    (hfourth : ∀ᶠ m : ℕ in atTop,
      ∃ Q : ℝ, 0 ≤ Q ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv
              (fun x =>
                deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) x) y‖
            ≤ Q) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (((Q * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
              (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ E : ℝ, 0 ≤ E ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y -
            deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z‖ ≤ E) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          ((E * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ := by
  filter_upwards [hfourth] with m hm
  rcases hm with ⟨Q, hQ, hbound, hsmall⟩
  let rad : ℝ := ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ
  have hrad : 0 ≤ rad := by
    dsimp [rad]
    exact mul_nonneg (norm_nonneg _) hρ
  refine ⟨Q * rad, mul_nonneg hQ hrad, ?_, ?_⟩
  · exact deriv_variation_le_of_deriv_bound_closedBall
      (G := fun w => deriv (fun v => deriv (fun u => deriv ((quadratic c)^[n + m]) u) v) w)
      (z := z) (r := rad) (M := Q) hrad hQ
      (fun y _hy =>
        ((((analyticAt_quadratic_iterate c (n + m) y).deriv).deriv).deriv.differentiableAt))
      (by simpa [rad] using hbound)
  · simpa [rad] using hsmall

/-- Fixed-tail base-centered second-derivative window from a third-derivative bound.

This packages the current remaining analytic task in the sharp form: the caller supplies a
third-derivative bound on the shrinking ball and its scalar smallness; the base fixed-tail
second-derivative contribution is discharged internally. -/
theorem eventually_base_center_second_deriv_bound_of_repelling_hit_third_deriv
    {c z α : ℂ} {n : ℕ} {C ρ r μ₀ μ₁ μ : ℝ}
    (hhit : (quadratic c)^[n] z = α)
    (hfix : quadratic c α = α)
    (hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0)
    (hrep : 1 < ‖(2 : ℂ) * α‖)
    (hCnonneg : 0 ≤ C)
    (hC : 2 ≤ C * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1))
    (hρ : 0 ≤ ρ)
    (hr : 0 ≤ r)
    (hCr : C * r < μ₀)
    (hthird : ∀ᶠ m : ℕ in atTop,
      ∃ T : ℝ, 0 ≤ T ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y‖ ≤ T) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          ((T * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ)) *
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ₁)
    (hsum : μ₀ + μ₁ ≤ μ) :
    ∀ᶠ m : ℕ in atTop,
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ y ∈ Metric.closedBall z
            (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * ρ),
          ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
        ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
          (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ :=
  eventually_base_center_second_deriv_bound_of_repelling_hit_excess
    (c := c) (z := z) (α := α) (n := n) (C := C) (ρ := ρ)
    (r := r) (μ₀ := μ₀) (μ₁ := μ₁) (μ := μ)
    hhit hfix hinit hrep hCnonneg hC hr hCr
    (eventually_second_deriv_excess_of_third_deriv_bound
      (c := c) (z := z) (n := n) (ρ := ρ) (r := r) (μ := μ₁) hρ hthird)
    hsum

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

/-- Selector bridge for an inverse-multiplier scaled Newton window at an arbitrary fixed scaled
center `τ`, with geometric containment automatic.  The Poincare/Hurwitz side only has to produce
the Newton center, center-fit, and derivative-variation estimates; inverse-multiplier shrinkage
puts the scaled window back into the requested physical ball. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_auto_containment_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ : ℝ) (K : NNReal),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall τ r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) τ‖ ≤ μ) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_displacement_inv_deriv_window_half
    hαfix hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter, hvar, hsmall⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
    (orbitProduct_ne_zero_iff_no_precritical c z n).2
      (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit)
  have hcontain :
      ∀ᶠ m : ℕ in atTop,
        ∀ t ∈ Metric.closedBall τ r,
          z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t ∈ Metric.ball z₀ R :=
    eventually_inverse_scaled_closedBall_subset_ball_of_repelling_hit_center
      (c := c) (ζ := z₀) (z := z) (α := α) (τ := τ) (n := n)
      (R := R) (r := r) hhit hαfix hinit hαrep hz hr
  filter_upwards [hderiv, hcenter, hvar, hsmall, hcontain] with
    m hderiv_m hcenter_m hvar_m hsmall_m hcontain_m
  exact ⟨τ, (deriv ((quadratic c)^[n + m]) z)⁻¹, r, μ, K,
    hr, hμ, hderiv_m, hcontain_m, hK, hcenter_m, hvar_m, hsmall_m⟩

/-- Arbitrary-center selector bridge where the local input is only a tail-by-tail
second-derivative bound on the corresponding shrinking physical balls. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_eventual_second_deriv_auto_containment_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ : ℝ) (K : NNReal),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∃ B : ℝ, 0 ≤ B ∧
              (∀ y ∈ Metric.closedBall
                  (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r),
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_auto_containment_half_not_postcritical
    hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter, hsecond, hsmall⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  exact ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter,
    eventually_scaled_deriv_variation_of_eventual_second_deriv_bound_center
      (c := c) (z := z) (τ := τ) (n := n) (r := r) (μ := μ) hr hsecond,
    hsmall⟩

/-- Arbitrary-center selector bridge with a base-centered second-derivative window.

The local analytic input is now stated on the single shrinking physical ball
`closedBall z (‖D⁻¹‖ * (‖τ‖ + r))`.  This is the uniform-control form needed before proving the
actual fixed-tail/Poincare window. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_eventual_second_deriv_base_auto_containment_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ : ℝ) (K : NNReal),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∃ B : ℝ, 0 ≤ B ∧
              (∀ y ∈ Metric.closedBall z
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r)),
                ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ B) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                (B * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_auto_containment_half_not_postcritical
    hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter, hsecond, hsmall⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  exact ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter,
    eventually_scaled_deriv_variation_of_eventual_second_deriv_bound_center_base
      (c := c) (z := z) (τ := τ) (n := n) (r := r) (μ := μ) hr hsecond,
    hsmall⟩

/-- Arbitrary-center selector bridge from a base-centered third-derivative window.

The base fixed-tail second-derivative contribution is discharged internally.  The remaining local
analytic input is only the third-derivative bound on
`closedBall z (‖D⁻¹‖ * (‖τ‖ + r))` and its scalar smallness. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_third_deriv_base_auto_containment_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ₀ μ₁ μ : ℝ) (K : NNReal) (C : ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧ 0 ≤ C ∧
          2 ≤ C * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1) ∧
          C * r < μ₀ ∧ μ₀ + μ₁ ≤ μ ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∃ T : ℝ, 0 ≤ T ∧
              (∀ y ∈ Metric.closedBall z
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r)),
                ‖deriv
                    (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y‖ ≤ T) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                ((T * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r))) *
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ₁) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply
    forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_eventual_second_deriv_base_auto_containment_half_not_postcritical
      hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨τ, r, μ₀, μ₁, μ, K, C,
      hr, hμ, hK, hCnonneg, hC, hCr, hsum, hderiv, hcenter, hthird, hsmall⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
    (orbitProduct_ne_zero_iff_no_precritical c z n).2
      (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit)
  have hρbase : 0 ≤ ‖τ‖ + r := by
    nlinarith [norm_nonneg τ, hr]
  refine ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter, ?_, hsmall⟩
  exact eventually_base_center_second_deriv_bound_of_repelling_hit_third_deriv
    (c := c) (z := z) (α := α) (n := n) (C := C) (ρ := ‖τ‖ + r)
    (r := r) (μ₀ := μ₀) (μ₁ := μ₁) (μ := μ)
    hhit hαfix hinit hαrep hCnonneg hC hρbase hr hCr hthird hsum

/-- Arbitrary-center selector bridge from a base-centered third-derivative excess window.

Compared with
`forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_third_deriv_base_auto_containment_half_not_postcritical`,
the caller no longer supplies the full third-derivative bound.  The basepoint third-derivative term
is discharged internally from the repelling fixed tail, leaving only the local oscillation of the
third-derivative function on the shrinking base-centered ball. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_third_deriv_excess_auto_containment_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ₂base μ₃base μ₃excess μ : ℝ) (K : NNReal) (C₂ C₃ : ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          0 ≤ C₂ ∧
          2 ≤ C₂ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1) ∧
          0 ≤ C₃ ∧
          6 * C₂ ≤ C₃ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 2 - 1) ∧
          C₂ * r < μ₂base ∧
          C₃ * (‖τ‖ + r) * r < μ₃base ∧
          μ₂base + (μ₃base + μ₃excess) ≤ μ ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∃ E : ℝ, 0 ≤ E ∧
              (∀ y ∈ Metric.closedBall z
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r)),
                ‖deriv
                    (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) y -
                  deriv
                    (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) z‖ ≤ E) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                ((E * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r))) *
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ₃excess) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply
    forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_eventual_second_deriv_base_auto_containment_half_not_postcritical
      hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨τ, r, μ₂base, μ₃base, μ₃excess, μ, K, C₂, C₃,
      hr, hμ, hK, hC₂nonneg, hC₂, hC₃nonneg, hC₃, hC₂r,
      hC₃ρr, hsum, hderiv, hcenter, hexcess, hsmall⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hinit : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z) ≠ 0 :=
    (orbitProduct_ne_zero_iff_no_precritical c z n).2
      (no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit)
  have hρbase : 0 ≤ ‖τ‖ + r := by
    nlinarith [norm_nonneg τ, hr]
  refine ⟨τ, r, μ, K, hr, hμ, hK, hderiv, hcenter, ?_, hsmall⟩
  exact eventually_base_center_second_deriv_bound_of_repelling_hit_third_deriv
    (c := c) (z := z) (α := α) (n := n) (C := C₂) (ρ := ‖τ‖ + r)
    (r := r) (μ₀ := μ₂base) (μ₁ := μ₃base + μ₃excess) (μ := μ)
    hhit hαfix hinit hαrep hC₂nonneg hC₂ hρbase hr hC₂r
    (eventually_base_center_third_deriv_bound_of_repelling_hit_excess
      (c := c) (z := z) (α := α) (n := n) (C₂ := C₂) (C₃ := C₃)
      (ρ := ‖τ‖ + r) (r := r) (μ₀ := μ₃base) (μ₁ := μ₃excess)
      (μ := μ₃base + μ₃excess)
      hhit hαfix hinit hαrep hC₂nonneg hC₂ hC₃nonneg hC₃ hρbase hr hC₃ρr
      hexcess le_rfl)
    hsum

/-- Arbitrary-center selector bridge from a base-centered fourth-derivative window.

This is the first derivative-only version of the fixed-tail local input after the basepoint terms are
discharged: a fourth-derivative bound on the shrinking physical ball controls the third-derivative
oscillation, which in turn controls the second-derivative Newton window. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_fourth_deriv_auto_containment_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ₂base μ₃base μ₃excess μ : ℝ) (K : NNReal) (C₂ C₃ : ℝ),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          0 ≤ C₂ ∧
          2 ≤ C₂ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ - 1) ∧
          0 ≤ C₃ ∧
          6 * C₂ ≤ C₃ * ‖(2 : ℂ) * α‖ * (‖(2 : ℂ) * α‖ ^ 2 - 1) ∧
          C₂ * r < μ₂base ∧
          C₃ * (‖τ‖ + r) * r < μ₃base ∧
          μ₂base + (μ₃base + μ₃excess) ≤ μ ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∃ Q : ℝ, 0 ≤ Q ∧
              (∀ y ∈ Metric.closedBall z
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r)),
                ‖deriv
                    (fun x =>
                      deriv
                        (fun w => deriv (fun v => deriv ((quadratic c)^[n + m]) v) w) x) y‖
                  ≤ Q) ∧
              ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ *
                (((Q * (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r))) *
                    (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (‖τ‖ + r))) *
                  (‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * r)) ≤ μ₃excess) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ))) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply
    forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_third_deriv_excess_auto_containment_half_not_postcritical
      hαfix hαrep hαcrit
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  obtain ⟨τ, r, μ₂base, μ₃base, μ₃excess, μ, K, C₂, C₃,
      hr, hμ, hK, hC₂nonneg, hC₂, hC₃nonneg, hC₃, hC₂r,
      hC₃ρr, hsum, hderiv, hcenter, hfourth, hsmall⟩ :=
    hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzfrontHit
  have hρbase : 0 ≤ ‖τ‖ + r := by
    nlinarith [norm_nonneg τ, hr]
  exact ⟨τ, r, μ₂base, μ₃base, μ₃excess, μ, K, C₂, C₃,
    hr, hμ, hK, hC₂nonneg, hC₂, hC₃nonneg, hC₃, hC₂r,
    hC₃ρr, hsum, hderiv, hcenter,
    eventually_third_deriv_excess_of_fourth_deriv_bound
      (c := c) (z := z) (n := n) (ρ := ‖τ‖ + r) (r := r) (μ := μ₃excess)
      hρbase hfourth,
    hsmall⟩

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

/-- q62 target-density reduction from an arbitrary-center inverse-multiplier scaled Newton window.
The geometric target-ball containment is supplied internally by fixed-tail derivative growth. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_scaled_inv_deriv_window_auto_containment_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∃ (τ : ℂ) (r μ : ℝ) (K : NNReal),
          0 ≤ r ∧ 0 ≤ μ ∧ K < 1 ∧
          (∀ᶠ m : ℕ in atTop,
            deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ ≠ 0) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
              ‖(quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * τ)‖ ≤
                (1 - (K : ℝ)) * r) ∧
          (∀ᶠ m : ℕ in atTop,
            ∀ t ∈ Metric.closedBall τ r,
              ‖deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) t -
                deriv
                  (fun u => (quadratic c)^[n + m]
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u) -
                    (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * u)) τ‖ ≤ μ) ∧
          (∀ᶠ m : ℕ in atTop,
            ‖(deriv
              (fun t => (quadratic c)^[n + m]
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t) -
                (z + (deriv ((quadratic c)^[n + m]) z)⁻¹ * t)) τ)⁻¹‖ *
                μ ≤ (K : ℝ)))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_scaled_inv_deriv_window_auto_containment_half_not_postcritical
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
