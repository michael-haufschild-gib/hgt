import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSqrtScaleEscape
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePForcedLocalRecurrence

/-!
# Unbounded local Route-P flux slope on the physical square-root clock

The normalized physical history has arbitrarily deep negative excursions per
square-root wall scale. Its successor difference is the literal one-atom flux.
If that flux had an eventual lower slope bound relative to the square-root
clock, the history plus a fixed clock multiple would be eventually monotone,
contradicting the source escape. Zero-atom flux is exactly zero, so all forced
negative slope witnesses are prime-power admissions.

This rules out a uniformly Lipschitz lower response in the physical clock. It
does not supply a sign-selected debt payment or a cofinal meromorphic graph.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Physical endpoint square-root clock for the finite source head. -/
def routePPhysicalRootClock (K : ℕ) : ℝ :=
  Real.sqrt ((K + 2 : ℕ) : ℝ)

private theorem routePPhysicalRootClock_one_le (K : ℕ) :
    1 ≤ routePPhysicalRootClock K := by
  unfold routePPhysicalRootClock
  have h : (1 : ℝ) ≤ ((K + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ K + 2 by omega)
  simpa using Real.sqrt_le_sqrt h

private theorem routePPhysicalRootClock_step_nonneg (K : ℕ) :
    0 ≤ routePPhysicalRootClock (K + 1) - routePPhysicalRootClock K := by
  unfold routePPhysicalRootClock
  have h : (((K + 2 : ℕ) : ℝ)) ≤ ((K + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show K + 2 ≤ K + 3 by omega)
  have hs := Real.sqrt_le_sqrt h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (sub_nonneg.mpr hs)

/-- No fixed lower slope controls all late normalized source-history fluxes. -/
theorem routeP_cofinal_flux_below_any_root_clock_slope
    (B : ℝ) (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K <
        -B * (routePPhysicalRootClock (K + 1) - routePPhysicalRootClock K) := by
  by_contra hnone
  push Not at hnone
  let Q : ℕ → ℝ := ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect
  let F : ℕ → ℝ := fun K => Q K + B * routePPhysicalRootClock K
  have hstep (K : ℕ) (hK : M ≤ K) : F K ≤ F (K + 1) := by
    have hflux := hnone K hK
    have hdiff :=
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceDefect_succ_sub_eq_flux K
    dsimp only [F, Q]
    linarith
  have hmono (K : ℕ) (hK : M ≤ K) : F M ≤ F K := by
    induction K, hK using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact ih.trans (hstep n hn)
  let D : ℝ := max (-(F M)) 0
  let B₀ : ℝ := max B 0
  let C : ℝ := -(D + B₀ + 1)
  obtain ⟨K, hK, hescape⟩ :=
    routeP_normalized_history_sqrt_scale_cofinally_unbounded_below C M
  have hF := hmono K hK
  have hD : -D ≤ F M := by
    have := le_max_left (-(F M)) 0
    dsimp only [D]
    linarith
  have hD0 : 0 ≤ D := le_max_right _ _
  have hB : B ≤ B₀ := le_max_left _ _
  have hr : 1 ≤ routePPhysicalRootClock K :=
    routePPhysicalRootClock_one_le K
  have hDscale : D ≤ D * routePPhysicalRootClock K := by
    nlinarith only [hr, hD0]
  have hBscale : B * routePPhysicalRootClock K ≤
      B₀ * routePPhysicalRootClock K :=
    mul_le_mul_of_nonneg_right hB (by linarith : 0 ≤ routePPhysicalRootClock K)
  dsimp only [F, Q] at hF
  change Q K < C * routePPhysicalRootClock K at hescape
  dsimp only [C] at hescape
  have hrootpos : 0 < routePPhysicalRootClock K := by linarith
  nlinarith only [hF, hD, hDscale, hBscale, hescape, hrootpos]

/-- The forced arbitrarily steep negative flux occurs at prime-power admissions,
not at the zero atoms absorbed by the moving terminal connection. -/
theorem routeP_cofinal_primePower_flux_below_any_root_clock_slope
    (B : ℝ) (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧ IsPrimePow (K + 3) ∧
      ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K <
        -B * (routePPhysicalRootClock (K + 1) - routePPhysicalRootClock K) := by
  let P : ℝ := max B 0 + 1
  obtain ⟨K, hK, hflux⟩ := routeP_cofinal_flux_below_any_root_clock_slope P M
  have hstep := routePPhysicalRootClock_step_nonneg K
  have hP : 0 < P := by dsimp only [P]; have := le_max_right B 0; linarith
  have hB : B ≤ P := by dsimp only [P]; have := le_max_left B 0; linarith
  have hnegative : ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux K < 0 := by
    nlinarith only [hflux, hP, hstep]
  have hpp : IsPrimePow (K + 3) := by
    by_contra hnot
    have hz := ccmActualHeadMatchedQuantileParabolicNormalizedVarianceFlux_eq_zero_of_not_isPrimePow K hnot
    linarith
  refine ⟨K, hK, hpp, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hB hstep
  nlinarith only [hflux, hmul]

end

end RHTower
