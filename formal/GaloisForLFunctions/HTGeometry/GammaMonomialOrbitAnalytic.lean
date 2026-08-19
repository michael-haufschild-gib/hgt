import GaloisForLFunctions.HTGeometry.GammaMonomialOrbitMajorant
import GaloisForLFunctions.HTGeometry.GammaMonomialNotRational

/-!
# The orbit limit is analytic

The orbit series has analytic terms and, by the majorant of `GammaMonomialOrbitMajorant`, converges
locally uniformly on the half plane.  So its sum is differentiable there — the second hypothesis of
`eq_zero_of_periodic_of_vertical_decay`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem analyticAt_orbitFactor {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (j : ℕ) {s : ℂ}
    (hz : ∀ k, s + (j : ℂ) + lam k ≠ 0) :
    AnalyticAt ℂ (fun u : ℂ => ∏ k, (u + (j : ℂ) + lam k) ^ (g k)) s := by
  have hprod0 : AnalyticAt ℂ
      (∏ k : Fin r, fun u : ℂ => (u + ((j : ℂ) + lam k)) ^ (g k)) s := by
    refine Finset.analyticAt_prod _ fun k _ => ?_
    refine analyticAt_shift_zpow ((j : ℂ) + lam k) (g k) ?_
    have := hz k
    rw [← add_assoc]
    exact this
  have hfun : (∏ k : Fin r, fun u : ℂ => (u + ((j : ℂ) + lam k)) ^ (g k))
      = fun u : ℂ => ∏ k, (u + (j : ℂ) + lam k) ^ (g k) := by
    funext u
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl fun k _ => by rw [add_assoc]
  rwa [hfun] at hprod0

theorem analyticAt_gammaMonomial_shift {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (j : ℕ) {s : ℂ}
    (hs : (∑ i, |(lam i).re|) < (s + (j : ℂ)).re) :
    AnalyticAt ℂ (fun u : ℂ => gammaMonomial lam g (u + (j : ℂ))) s := by
  have hshift : AnalyticAt ℂ (fun u : ℂ => u + (j : ℂ)) s := analyticAt_id.add analyticAt_const
  have hc := AnalyticAt.comp (g := gammaMonomial lam g) (f := fun u : ℂ => u + (j : ℂ)) (x := s)
    (analyticAt_gammaMonomial_of_gt_sum_abs lam g hs) hshift
  have hrw : (gammaMonomial lam g ∘ fun u : ℂ => u + (j : ℂ))
      = fun u : ℂ => gammaMonomial lam g (u + (j : ℂ)) := by funext u; rfl
  rwa [hrw] at hc

theorem analyticAt_orbitTerm {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) (j : ℕ) {s : ℂ}
    (hs : (∑ i, |(lam i).re|) < s.re) :
    AnalyticAt ℂ (fun u : ℂ => orbitTerm lam g u j) s := by
  have hjs : (∑ i, |(lam i).re|) < (s + (j : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hz : ∀ k, s + (j : ℂ) + lam k ≠ 0 := by
    intro k hcon
    have := re_pos_of_gt_sum_abs lam hjs k
    rw [hcon] at this
    simp at this
  have h1 := analyticAt_orbitFactor lam g j hz
  have h2 := analyticAt_gammaMonomial_shift lam g j hjs
  have h3 : AnalyticAt ℂ
      (fun u : ℂ => (∏ k, (u + (j : ℂ) + lam k) ^ (g k)) - 1) s := h1.sub analyticAt_const
  exact h3.mul h2

/-- **The orbit limit is differentiable on the half plane.** -/
theorem differentiableOn_gammaMonomialOrbitLimit {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ)
    (hdeg : ∑ k, g k = 0) (hmom : ∑ k, (g k : ℂ) * lam k = 0) :
    ∃ Rb : ℝ, 1 ≤ Rb ∧ DifferentiableOn ℂ (gammaMonomialOrbitLimit lam g)
      {s : ℂ | (∑ j, |(lam j).re|) < s.re ∧ Rb < ‖s‖} := by
  obtain ⟨D, Rb, hD0, hRb, hD⟩ := exists_orbitTerm_majorant lam g hdeg hmom
  set U : Set ℂ := {s : ℂ | (∑ j, |(lam j).re|) < s.re ∧ Rb < ‖s‖} with hU
  have hUopen : IsOpen U := by
    have h1 : IsOpen {s : ℂ | (∑ j, |(lam j).re|) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {s : ℂ | Rb < ‖s‖} := isOpen_lt continuous_const continuous_norm
    exact h1.inter h2
  have hterm : ∀ j : ℕ, DifferentiableOn ℂ (fun u : ℂ => orbitTerm lam g u j) U := by
    intro j s hs
    exact (analyticAt_orbitTerm lam g j hs.1).differentiableAt.differentiableWithinAt
  have hMdiff : DifferentiableOn ℂ (gammaMonomial lam g) U := by
    intro s hs
    exact (analyticAt_gammaMonomial_of_gt_sum_abs lam g hs.1).differentiableAt.differentiableWithinAt
  have hloc : SummableLocallyUniformlyOn (fun j (s : ℂ) => orbitTerm lam g s j) U := by
    refine summableLocallyUniformlyOn_of_locally_bounded fun s₀ hs₀ => ?_
    obtain ⟨δ, hδ0, hball⟩ := Metric.isOpen_iff.mp hUopen s₀ hs₀
    have hcball : Metric.closedBall s₀ (δ / 2) ⊆ U := by
      refine subset_trans (Metric.closedBall_subset_ball (by linarith)) hball
    obtain ⟨Msup, hMsup⟩ := (isCompact_closedBall s₀ (δ / 2)).exists_bound_of_continuousOn
      ((hMdiff.mono hcball).continuousOn)
    refine ⟨Metric.ball s₀ (δ / 2), ?_,
      fun j => D * Msup * (1 / ((j : ℝ) + 1) ^ 2), ?_, ?_⟩
    · exact nhdsWithin_le_nhds (Metric.ball_mem_nhds s₀ (by linarith))
    · exact (summable_inv_succ_sq.mul_left (D * Msup))
    · intro j y hy
      have hyc : y ∈ Metric.closedBall s₀ (δ / 2) := Metric.ball_subset_closedBall hy
      have hyU : y ∈ U := hcball hyc
      have hb := hD y hyU.1 (le_of_lt hyU.2) j
      have hMy : ‖gammaMonomial lam g y‖ ≤ Msup := hMsup y hyc
      have hnn : (0 : ℝ) ≤ D * (1 / ((j : ℝ) + 1) ^ 2) := by positivity
      calc ‖orbitTerm lam g y j‖
          ≤ D * ‖gammaMonomial lam g y‖ * (1 / ((j : ℝ) + 1) ^ 2) := hb
        _ ≤ D * Msup * (1 / ((j : ℝ) + 1) ^ 2) := by
            have h1 : D * ‖gammaMonomial lam g y‖ ≤ D * Msup :=
              mul_le_mul_of_nonneg_left hMy hD0
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have hsumdiff : DifferentiableOn ℂ (fun s : ℂ => ∑' j : ℕ, orbitTerm lam g s j) U := by
    refine (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      hloc.hasSumLocallyUniformlyOn).differentiableOn ?_ hUopen
    refine Filter.Eventually.of_forall fun S => ?_
    exact DifferentiableOn.fun_sum fun j _ => hterm j
  exact ⟨Rb, hRb, hMdiff.add hsumdiff⟩

end

end GaloisForLFunctions.HTGeometry
