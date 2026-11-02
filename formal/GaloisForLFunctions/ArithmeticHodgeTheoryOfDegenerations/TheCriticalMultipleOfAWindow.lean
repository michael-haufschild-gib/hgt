import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonCriterion

/-!
# The critical multiple of a window

The horizon theorem identifies the second-order term of the degeneration on a horizon window with
`κ_φ Q(H)`, up to `K/K_c` at the multiple `K_c` of the critical curve `c^p = K_c log N`. Read through
the critical-multiple calculus:

* **A fixed multiple is sub-RH** (`weilQuad_halfWeight_ge_of_horizon_nonneg`): if the horizon block of
  `h` is eventually nonnegative along a schedule at the multiple `K_c`, then
  `κ_φ Q(H) ≥ −K/K_c`. Positivity at one multiple controls Weil's form on every window only up to
  `O(1/K_c)`.
* **Every negative window has a finite critical multiple** (`eventually_horizon_neg_of_weilQuad_neg`):
  if `Q(H) < 0`, then along every schedule at a multiple `K_c > K/(κ_φ |Q(H)|)` the horizon block is
  eventually negative.

An off-line zero is seen by some window (Weil's criterion), hence at a finite multiple of the
critical curve; under RH no window has a critical multiple.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri Zeta23

variable {h : ℝ → ℝ} {A : ℝ}

/-- **A fixed multiple is sub-RH.** -/
theorem weilQuad_halfWeight_ge_of_horizon_nonneg {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℕ → ℝ, (∀ N, 0 < c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ Kc : ℝ, 0 < Kc → Tendsto (fun N : ℕ => c N ^ p / Real.log N) atTop (𝓝 Kc) →
      (∀ᶠ N : ℕ in atTop, 0 ≤ (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) →
      -(K / Kc) ≤ (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h) := by
  obtain ⟨K, hK0, hK⟩ := horizon_layer_criticalCurve hφ hφsupp hφ2 hp hCφ hdecay hh hA hsupp
  refine ⟨K, hK0, fun c hc hcN Kc hKc hcrit hnn => ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨N, hN1, hN2⟩ := ((hK c hc hcN Kc hKc hcrit (ε / 2) (by linarith)).and hnn).exists
  have := (abs_le.mp hN1).2
  linarith

/-- **Every negative window has a finite critical multiple.** -/
theorem eventually_horizon_neg_of_weilQuad_neg {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 1 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℕ → ℝ, (∀ N, 0 < c N) → Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      ∀ Kc : ℝ, 0 < Kc → Tendsto (fun N : ℕ => c N ^ p / Real.log N) atTop (𝓝 Kc) →
      K / Kc < -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h)) →
      ∀ᶠ N : ℕ in atTop, (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2) < 0 := by
  obtain ⟨K, hK0, hK⟩ := horizon_layer_criticalCurve hφ hφsupp hφ2 hp hCφ hdecay hh hA hsupp
  refine ⟨K, hK0, fun c hc hcN Kc hKc hcrit hgap => ?_⟩
  set δ := -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * weilQuad (halfWeight h)) - K / Kc with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  filter_upwards [hK c hc hcN Kc hKc hcrit (δ / 2) (half_pos hδ0)] with N hN
  have := (abs_le.mp hN).2
  linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
