import GaloisForLFunctions.HTGeometry.KoenigsLinearizationGerm
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# The Poincaré function of a germ

Inverting a normalized Koenigs linearizer turns the linearizing equation `κ ∘ g = μ · κ` into the
Poincaré equation `Φ (μ w) = g (Φ w)`.  The inverse exists and is holomorphic because the linearizer
has derivative one at the fixed point.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **The Poincaré function.**  A normalized linearizer of a germ has a local inverse `Φ` with
`Φ 0 = 0`, `Φ' 0 = 1`, which conjugates multiplication by the multiplier back to the germ. -/
theorem exists_poincare_of_linearizer {g κ : ℂ → ℂ} {μ : ℂ}
    (hκ0 : κ 0 = 0) (hκd : HasStrictDerivAt κ 1 0)
    (hg0 : g 0 = 0) (hgc : ContinuousAt g 0)
    (hsemi : ∀ᶠ z in 𝓝 (0 : ℂ), κ (g z) = μ * κ z) :
    ∃ Φ : ℂ → ℂ, Φ 0 = 0 ∧ HasStrictDerivAt Φ 1 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), κ (Φ w) = w) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), Φ (μ * w) = g (Φ w)) := by
  have hone : (1 : ℂ) ≠ 0 := one_ne_zero
  set Φ : ℂ → ℂ := hκd.localInverse κ 1 0 hone with hΦdef
  have hleft : ∀ᶠ x in 𝓝 (0 : ℂ), Φ (κ x) = x := hκd.eventually_left_inverse hone
  have hright0 : ∀ᶠ x in 𝓝 (κ 0), κ (Φ x) = x := hκd.eventually_right_inverse hone
  rw [hκ0] at hright0
  have hΦ0 : Φ 0 = 0 := by
    have h := hleft.self_of_nhds
    rwa [hκ0] at h
  have hΦd : HasStrictDerivAt Φ 1 0 := by
    have h := hκd.to_localInverse hone
    rw [hκ0, inv_one] at h
    exact h
  have hΦc : ContinuousAt Φ 0 := hΦd.hasDerivAt.continuousAt
  have htΦ : Tendsto Φ (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have := hΦc.tendsto
    rwa [hΦ0] at this
  have htg : Tendsto g (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have := hgc.tendsto
    rwa [hg0] at this
  have htmul : Tendsto (fun w : ℂ => μ * w) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h : Tendsto (fun w : ℂ => μ * w) (𝓝 (0 : ℂ)) (𝓝 (μ * 0)) :=
      ((continuous_const (y := μ)).mul continuous_id).tendsto 0
    simpa using h
  refine ⟨Φ, hΦ0, hΦd, hright0, ?_⟩
  -- the four eventual facts along `w`
  have e1 : ∀ᶠ w in 𝓝 (0 : ℂ), κ (g (Φ w)) = μ * κ (Φ w) := htΦ.eventually hsemi
  have e2 : ∀ᶠ w in 𝓝 (0 : ℂ), κ (Φ w) = w := hright0
  have e3 : ∀ᶠ w in 𝓝 (0 : ℂ), κ (Φ (μ * w)) = μ * w := htmul.eventually hright0
  have e4 : ∀ᶠ w in 𝓝 (0 : ℂ), Φ (κ (g (Φ w))) = g (Φ w) :=
    (htg.comp htΦ).eventually hleft
  have e5 : ∀ᶠ w in 𝓝 (0 : ℂ), Φ (κ (Φ (μ * w))) = Φ (μ * w) :=
    ((htΦ.comp htmul)).eventually hleft
  filter_upwards [e1, e2, e3, e4, e5] with w h1 h2 h3 h4 h5
  have hval : κ (g (Φ w)) = κ (Φ (μ * w)) := by rw [h1, h2, h3]
  calc Φ (μ * w) = Φ (κ (Φ (μ * w))) := h5.symm
    _ = Φ (κ (g (Φ w))) := by rw [hval]
    _ = g (Φ w) := h4

/-- The Poincaré function attached to the Koenigs linearizer of an attracting germ. -/
theorem exists_poincare_koenigs {g : ℂ → ℂ} {μ : ℂ} {K c r : ℝ}
    (hμ : μ ≠ 0) (hK0 : 0 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hq : c ^ (2 : ℕ) < ‖μ‖) (hr : 0 < r)
    (hgd : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) r))
    (hquad : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z - μ * z‖ ≤ K * ‖z‖ ^ (2 : ℕ))
    (hgc : ∀ z : ℂ, ‖z‖ ≤ r → ‖g z‖ ≤ c * ‖z‖)
    (hg0 : g 0 = 0) (hga : HasDerivAt g μ 0) :
    ∃ Φ : ℂ → ℂ, Φ 0 = 0 ∧ HasStrictDerivAt Φ 1 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), koenigsGerm g μ (Φ w) = w) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), Φ (μ * w) = g (Φ w)) := by
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds _ hr
  have hκ0 : koenigsGerm g μ 0 = 0 :=
    koenigsGerm_zero hμ hK0 hc0 hc1 hq hquad hgc hr.le hg0
  have hκan : AnalyticAt ℂ (koenigsGerm g μ) 0 := by
    have hdiff := koenigsGerm_differentiableOn hμ hK0 hc0 hc1 hq hr.le hgd hquad hgc
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) 0 (Metric.mem_ball_self hr)
  have hκd : HasStrictDerivAt (koenigsGerm g μ) 1 0 := by
    have h := hκan.hasStrictDerivAt
    rwa [deriv_koenigsGerm_zero hμ hK0 hc0 hc1 hq hr hgd hquad hgc hg0 hga] at h
  have hgcont : ContinuousAt g 0 := hga.continuousAt
  have hsemi : ∀ᶠ z in 𝓝 (0 : ℂ), koenigsGerm g μ (g z) = μ * koenigsGerm g μ z := by
    filter_upwards [hball] with z hz
    exact koenigsGerm_semiconj hμ hK0 hc0 hc1 hq hquad hgc
      (le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz))
  exact exists_poincare_of_linearizer hκ0 hκd hg0 hgcont hsemi

end

end GaloisForLFunctions.HTGeometry
