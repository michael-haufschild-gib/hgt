import GaloisForLFunctions.Bottcher.JuliaFrontierPreimage
import GaloisForLFunctions.Bottcher.RelativeRigidityGlobalBranchDenseNonres

open Polynomial Filter Topology Set Metric

namespace Bottcher

noncomputable section

/-- If `α` is fixed, then `-α` maps to the same fixed point for `z ↦ z² + c`. -/
theorem quadratic_neg_fixed_eq_fixed {c α : ℂ} (hfix : quadratic c α = α) :
    quadratic c (-α) = α := by
  simpa [quadratic] using hfix

/-- A strictly repelling fixed point is nonzero. -/
theorem fixed_point_ne_zero_of_repelling {α : ℂ} (hrep : 1 < ‖(2 : ℂ) * α‖) :
    α ≠ 0 := by
  intro hα
  rw [hα, mul_zero, norm_zero] at hrep
  linarith

/-- The pair `α, -α` is distinct exactly when `α` is nonzero. -/
theorem fixed_point_ne_neg_of_ne_zero {α : ℂ} (hα0 : α ≠ 0) :
    α ≠ -α := by
  intro h
  apply hα0
  have htwo : (2 : ℂ) * α = 0 := by linear_combination h
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- One fixed anchor gives two target values, `α` and `-α`.  If the frontier ball already contains
`α`, we are done because `α` is fixed; if it contains `-α`, one iterate hits `α`; otherwise the
off-ball two-value selector forces a positive forward hit to one of them, and a hit to `-α` is
advanced by one more iterate. -/
theorem frontier_ball_positive_periodic_or_forward_hit_fixed_preimage_pair
    {c α z₀ : ℂ} {ρ Rlift : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαfix : quadratic c α = α) (hα0 : α ≠ 0) :
    (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
      ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α := by
  by_cases hαball : α ∈ ball z₀ Rlift
  · exact Or.inl ⟨1, α, by norm_num, hαball, by simpa using hαfix⟩
  by_cases hnegalpha_ball : -α ∈ ball z₀ Rlift
  · exact Or.inr ⟨1, -α, by norm_num, hnegalpha_ball,
      by simpa using quadratic_neg_fixed_eq_fixed hαfix⟩
  have hαneg : α ≠ -α := fixed_point_ne_neg_of_ne_zero hα0
  have hαout : ∀ z ∈ ball z₀ Rlift, z ≠ α := by
    intro z hz hza
    apply hαball
    rwa [← hza]
  have hnegout : ∀ z ∈ ball z₀ Rlift, z ≠ -α := by
    intro z hz hzneg
    apply hnegalpha_ball
    rwa [← hzneg]
  have hsel := frontier_ball_positive_periodic_or_forward_hit_value_pair_off_ball
    (c := c) (α := α) (β := -α) (z₀ := z₀) (ρ := ρ) (Rlift := Rlift)
    hzfront hρ0 hρR hαneg hαout hnegout
  rcases hsel with hper | hhit
  · exact Or.inl hper
  · obtain ⟨n, z, hn, hz, hval⟩ := hhit
    rcases hval with hvalα | hvalneg
    · exact Or.inr ⟨n, z, hn, hz, hvalα⟩
    · refine Or.inr ⟨n + 1, z, by omega, hz, ?_⟩
      rw [Function.iterate_succ_apply', hvalneg]
      exact quadratic_neg_fixed_eq_fixed hαfix

/-- Choosing the repelling fixed point supplied by `c ≠ 1/4`, every frontier ball either already
contains a positive periodic point or has a positive forward hit to that single fixed point. -/
theorem exists_repelling_fixed_frontier_ball_positive_periodic_or_forward_hit
    {c : ℂ} (hc : c ≠ 1 / 4) :
    ∃ α : ℂ,
      quadratic c α = α ∧ 1 < ‖(2 : ℂ) * α‖ ∧
        ∀ {z₀ : ℂ} {ρ Rlift : ℝ},
          z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < Rlift / 2 →
            (∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = z) ∨
              ∃ n z, 1 ≤ n ∧ z ∈ ball z₀ Rlift ∧ (quadratic c)^[n] z = α := by
  obtain ⟨α, hαfix, _hαK, hαrep⟩ := exists_repelling_fixed_point c hc
  refine ⟨α, hαfix, hαrep, ?_⟩
  intro z₀ ρ Rlift hzfront hρ0 hρR
  exact frontier_ball_positive_periodic_or_forward_hit_fixed_preimage_pair
    hzfront hρ0 hρR hαfix (fixed_point_ne_zero_of_repelling hαrep)

/-- The positive critical orbit cannot contain two distinct fixed points.  Once the critical orbit
reaches one fixed point, every later fixed-point occurrence must be the same point. -/
theorem fixed_points_mem_positiveCriticalOrbit_eq
    {c α β : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β)
    (hαcrit : α ∈ positiveCriticalOrbit c) (hβcrit : β ∈ positiveCriticalOrbit c) :
    α = β := by
  obtain ⟨i, hi⟩ := hαcrit
  obtain ⟨j, hj⟩ := hβcrit
  change (quadratic c)^[i + 1] 0 = α at hi
  change (quadratic c)^[j + 1] 0 = β at hj
  rcases le_total i j with hij | hji
  · symm
    have hdecomp : j + 1 = (j - i) + (i + 1) := by omega
    calc
      β = (quadratic c)^[j + 1] 0 := hj.symm
      _ = (quadratic c)^[(j - i) + (i + 1)] 0 := by rw [hdecomp]
      _ = (quadratic c)^[j - i] ((quadratic c)^[i + 1] 0) := by
        rw [Function.iterate_add_apply]
      _ = (quadratic c)^[j - i] α := by rw [hi]
      _ = α := Function.iterate_fixed hαfix (j - i)
  · have hdecomp : i + 1 = (i - j) + (j + 1) := by omega
    calc
      α = (quadratic c)^[i + 1] 0 := hi.symm
      _ = (quadratic c)^[(i - j) + (j + 1)] 0 := by rw [hdecomp]
      _ = (quadratic c)^[i - j] ((quadratic c)^[j + 1] 0) := by
        rw [Function.iterate_add_apply]
      _ = (quadratic c)^[i - j] β := by rw [hj]
      _ = β := Function.iterate_fixed hβfix (i - j)

/-- For `c ≠ 1/4`, at least one fixed point is outside the positive critical orbit. -/
theorem exists_fixed_point_not_mem_positiveCriticalOrbit
    (c : ℂ) (hc : c ≠ 1 / 4) :
    ∃ α : ℂ, quadratic c α = α ∧ α ∉ positiveCriticalOrbit c := by
  obtain ⟨α, β, hαfix, hβfix, hαβ⟩ := exists_two_distinct_fixed_points c hc
  by_cases hαcrit : α ∈ positiveCriticalOrbit c
  · refine ⟨β, hβfix, ?_⟩
    intro hβcrit
    exact hαβ (fixed_points_mem_positiveCriticalOrbit_eq hαfix hβfix hαcrit hβcrit)
  · exact ⟨α, hαfix, hαcrit⟩

/-- A distinct fixed pair exhausts all fixed points of a quadratic map. -/
theorem fixed_point_eq_left_or_right_of_fixed_pair
    {c α β γ : ℂ}
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hγfix : quadratic c γ = γ) :
    γ = α ∨ γ = β := by
  have hγαdiff : γ ^ 2 - α ^ 2 = γ - α := by
    have hγ : γ ^ 2 + c = γ := by simpa [quadratic] using hγfix
    have hα : α ^ 2 + c = α := by simpa [quadratic] using hαfix
    linear_combination hγ - hα
  have hγαprod : (γ - α) * (γ + α - 1) = 0 := by
    linear_combination hγαdiff
  have hβαdiff : β ^ 2 - α ^ 2 = β - α := by
    have hβ : β ^ 2 + c = β := by simpa [quadratic] using hβfix
    have hα : α ^ 2 + c = α := by simpa [quadratic] using hαfix
    linear_combination hβ - hα
  have hβαprod : (β - α) * (β + α - 1) = 0 := by
    linear_combination hβαdiff
  have hβsum : β + α - 1 = 0 := by
    rcases mul_eq_zero.mp hβαprod with hleft | hright
    · exact False.elim (hαβ (sub_eq_zero.mp hleft).symm)
    · exact hright
  rcases mul_eq_zero.mp hγαprod with hleft | hright
  · exact Or.inl (sub_eq_zero.mp hleft)
  · right
    linear_combination hright - hβsum

/-- In a distinct fixed pair for `c ≠ 1/4`, if the left fixed point is not repelling, then the
right fixed point is the repelling fixed point. -/
theorem fixed_pair_right_repelling_of_left_not_repelling
    {c α β : ℂ} (hc : c ≠ 1 / 4)
    (hαfix : quadratic c α = α) (hβfix : quadratic c β = β) (hαβ : α ≠ β)
    (hαnotrep : ¬ 1 < ‖(2 : ℂ) * α‖) :
    1 < ‖(2 : ℂ) * β‖ := by
  obtain ⟨γ, hγfix, _hγK, hγrep⟩ := exists_repelling_fixed_point c hc
  have hγ := fixed_point_eq_left_or_right_of_fixed_pair hαfix hβfix hαβ hγfix
  rcases hγ with rfl | rfl
  · exact False.elim (hαnotrep hγrep)
  · exact hγrep

/-- Half-radius density bridge for a single fixed anchor.  The selector uses the two target values
`α` and `-α`, but the caller only has to convert positive hits to `α`. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_fixed_preimage_pair_to_positive_periodic_half
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hα0 : α ≠ 0)
    (hhit : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ ball z₀ (R / 2) →
        (quadratic c)^[n] z = α →
        ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  intro z₀ hzfront R hR
  have hρ0 : 0 < R / 8 := by linarith
  have hρR : R / 8 < (R / 2) / 2 := by linarith
  have hsel := frontier_ball_positive_periodic_or_forward_hit_fixed_preimage_pair
    (c := c) (α := α) (z₀ := z₀) (ρ := R / 8) (Rlift := R / 2)
    hzfront hρ0 hρR hαfix hα0
  rcases hsel with hper | hhitcase
  · obtain ⟨n, z, hn, hz, hfix⟩ := hper
    have hzR : z ∈ ball z₀ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨z, hzR, n, hn, hfix⟩
  · obtain ⟨n, z, hn, hz, hval⟩ := hhitcase
    exact hhit hzfront hρ0 hρR n z hn hz hval

/-- Single-repelling-anchor fixed-tail Newton bridge.  This replaces the two-repelling-fixed-anchor
interface: the selector only needs the pair `α, -α`, while Newton uses the fixed tail at `α`. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hα0 : α ≠ 0) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_preimage_pair_to_positive_periodic_half
    hαfix hα0
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  obtain ⟨hprecrit, hwin⟩ := hwindow hzfront hρ0 hρR n z hn hz hhit
  exact exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_explicit_scaled_newton_window_half
    (c := c) (ζ := z₀) (z := z) (α := α) (n := n) (R := R)
    hn hhit hαfix ((orbitProduct_ne_zero_iff_no_precritical c z n).2 hprecrit)
    hαrep hz hwin

/-- Single-repelling-anchor fixed-tail bridge with the trivial anchor-hit case removed from the
Newton-window obligation.  If the selector hit has `z = α`, the anchor itself is already a positive
periodic point in the target ball; the hard fixed-tail window is only needed for `z ≠ α`. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical_ne
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hα0 : α ≠ 0) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_fixed_preimage_pair_to_positive_periodic_half
    hαfix hα0
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  by_cases hzα : z = α
  · subst z
    have hR0 : 0 < R := by linarith
    have hαR : α ∈ Metric.ball z₀ R := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    exact ⟨α, hαR, 1, by norm_num, by simpa using hαfix⟩
  · obtain ⟨hprecrit, hwin⟩ := hwindow hzfront hρ0 hρR n z hn hz hhit hzα
    exact exists_positive_periodic_point_mem_ball_of_repelling_fixed_hit_eventual_explicit_scaled_newton_window_half
      (c := c) (ζ := z₀) (z := z) (α := α) (n := n) (R := R)
      hn hhit hαfix ((orbitProduct_ne_zero_iff_no_precritical c z n).2 hprecrit)
      hαrep hz hwin

/-- Connected-empty-interior q62 target-density reduction from a single repelling fixed anchor and the
explicit fixed-tail Newton window.  The two-anchor repelling hypothesis is no longer needed. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical
      hαfix (fixed_point_ne_zero_of_repelling hαrep) hαrep hwindow)
    hE

/-- q62 target-density reduction with the trivial anchor-hit case removed from the fixed-tail Newton
window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical_ne_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α →
        (∀ k < n, (quadratic c)^[k] z ≠ 0) ∧
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical_ne
      hαfix (fixed_point_ne_zero_of_repelling hαrep) hαrep hwindow)
    hE

/-- If the chosen repelling fixed point is not in the positive critical orbit, the precritical
avoidance required by the fixed-tail Newton bridge is automatic.  The local input is then only the
explicit Newton window. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_not_postcritical
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α →
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical
    hαfix (fixed_point_ne_zero_of_repelling hαrep) hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit
  exact ⟨no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit,
    hwindow hzfront hρ0 hρR n z hn hz hhit⟩

/-- q62 target-density reduction for the non-postcritical repelling-fixed-anchor case.  The only
remaining local dynamical input is the explicit fixed-tail Newton window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_eventual_explicit_scaled_newton_window_half_not_postcritical_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α →
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_not_postcritical
      hαfix hαrep hαcrit hwindow)
    hE

/-- Non-postcritical q62 target-density reduction with the trivial `z = α` selector-hit case removed
from the explicit Newton-window obligation. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_eventual_explicit_scaled_newton_window_half_not_postcritical_ne_eventually_nonStrong_subset
    {c α : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hempty : interior (filledJulia c) = ∅)
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α →
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} := by
  apply dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical_ne_eventually_nonStrong_subset
    hconn hempty hαfix hαrep
  · intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα
    exact ⟨no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit,
      hwindow hzfront hρ0 hρR n z hn hz hhit hzα⟩
  · exact hE

/-- Non-postcritical fixed-anchor bridge where the local Newton window may use the additional fact
that the forward-hit preimage is itself on the Julia frontier. -/
theorem forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_frontier_hit_eventual_explicit_scaled_newton_window_half_not_postcritical_ne
    {c α : ℂ}
    (hαfix : quadratic c α = α) (hαrep : 1 < ‖(2 : ℂ) * α‖)
    (hαcrit : α ∉ positiveCriticalOrbit c)
    (hwindow : ∀ {z₀ : ℂ} {ρ R : ℝ},
      z₀ ∈ frontier (filledJulia c) → 0 < ρ → ρ < (R / 2) / 2 →
      ∀ n z, 1 ≤ n → z ∈ Metric.ball z₀ (R / 2) →
        (quadratic c)^[n] z = α → z ≠ α → z ∈ frontier (filledJulia c) →
        ∀ᶠ m : ℕ in atTop,
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ)) :
    ∀ z₀ ∈ frontier (filledJulia c), ∀ R : ℝ, 0 < R →
      ∃ y ∈ ball z₀ R, ∃ q : ℕ, 1 ≤ q ∧ (quadratic c)^[q] y = y := by
  apply forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_eventual_explicit_scaled_newton_window_half_no_precritical_ne
    hαfix (fixed_point_ne_zero_of_repelling hαrep) hαrep
  intro z₀ ρ R hzfront hρ0 hρR n z hn hz hhit hzα
  refine ⟨no_precritical_of_iterate_eq_not_mem_positiveCriticalOrbit hhit hαcrit, ?_⟩
  have hzHitFront : z ∈ frontier (filledJulia c) :=
    mem_frontier_of_forward_hit_repelling_fixed (c := c) (z := z) (α := α) (n := n)
      hhit hαfix hαrep
  exact hwindow hzfront hρ0 hρR n z hn hz hhit hzα hzHitFront

/-- q62 target-density reduction using the frontier status of each nontrivial fixed-anchor
forward-hit preimage as a proved input to the local Newton window. -/
theorem dense_nonresonantPeriodic_of_preconnected_emptyInterior_repelling_fixed_frontier_hit_eventual_explicit_scaled_newton_window_half_not_postcritical_ne_eventually_nonStrong_subset
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
          ∃ (r M : ℝ) (K : NNReal),
            0 ≤ r ∧ r ≤ R / 2 ∧ 0 ≤ M ∧ K < 1 ∧
            (‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ *
                ‖(2 : ℂ) * α‖ ^ m)⁻¹ * ‖α - z‖ ≤ (1 - (K : ℝ)) * r ∧
            (∀ y ∈ Metric.closedBall z r,
              ‖deriv (fun w => deriv ((quadratic c)^[n + m]) w) y‖ ≤ M) ∧
            ‖(deriv ((quadratic c)^[n + m]) z)⁻¹‖ * (M * r + 1) ≤ (K : ℝ))
    (hE : ∃ E : Finset ℂ, ∀ᶠ p : ℕ in atTop, nonStrongFixedPointRoots c p ⊆ E) :
    frontier (filledJulia c) ⊆ closure
      {z : ℂ | z ∈ frontier (filledJulia c) ∧ ∃ q : ℕ,
        (quadratic c)^[q] z = z ∧
        ∀ m : ℕ, 1 ≤ m →
          (deriv ((quadratic c)^[q]) z) ^ m ≠ ((2 ^ q : ℕ) : ℂ)} :=
  dense_nonresonantPeriodic_of_preconnected_emptyInterior_forall_frontier_ball_periodic_eventually_nonStrong_subset
    hconn hempty
    (forall_frontier_ball_positive_periodic_of_forward_hit_repelling_fixed_frontier_hit_eventual_explicit_scaled_newton_window_half_not_postcritical_ne
      hαfix hαrep hαcrit hwindow)
    hE

end

end Bottcher
