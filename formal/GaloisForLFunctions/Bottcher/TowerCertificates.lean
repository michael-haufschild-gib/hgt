/-
# Section loops and the tower winding calculus

Packaging for the band-tower induction: the canonical `C1Loop` traced by an analytic function on a
round circle, the doubling identity for windings of `θ ↦ δ(2θ)` (the shape of `f ∘ (section circle)`
under the tower functional equation), and the sublevel transport that reduces every inside-winding
query to the single evaluation at `0`.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.GreenSublevel
import GaloisForLFunctions.Bottcher.WindingCertificates

open Complex Set Filter Metric

namespace Bottcher

/-- The loop traced by an analytic `T` on the circle of radius `r`. -/
noncomputable def sectionLoop {T : ℂ → ℂ} {A : Set ℂ} {r : ℝ}
    (hT : AnalyticOnNhd ℂ T A) (hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ A) : C1Loop where
  γ := fun θ => T (circleMap 0 r θ)
  γ' := fun θ => deriv T (circleMap 0 r θ) * (circleMap 0 r θ * Complex.I)
  cont := by
    have h1 : ContinuousOn T A := hT.continuousOn
    exact h1.comp_continuous (continuous_circleMap 0 r) hcirc
  cont' := by
    have h1 : ContinuousOn (deriv T) A := (hT.deriv).continuousOn
    exact (h1.comp_continuous (continuous_circleMap 0 r) hcirc).mul
      ((continuous_circleMap 0 r).mul continuous_const)
  deriv := by
    intro θ _
    have h1 : HasDerivAt T (deriv T (circleMap 0 r θ)) (circleMap 0 r θ) :=
      (hT _ (hcirc θ)).differentiableAt.hasDerivAt
    have h2 := hasDerivAt_circleMap 0 r θ
    have h3 := h1.comp θ h2
    simpa using h3
  closed := by
    have : circleMap 0 r (2 * Real.pi) = circleMap 0 r 0 := by
      simpa using periodic_circleMap 0 r 0
    simp only [this]

theorem sectionLoop_γ {T : ℂ → ℂ} {A : Set ℂ} {r : ℝ}
    (hT : AnalyticOnNhd ℂ T A) (hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ A) (θ : ℝ) :
    (sectionLoop hT hcirc).γ θ = T (circleMap 0 r θ) := rfl

/-- A section loop at constant Green level avoids every point at a different level. -/
theorem sectionLoop_avoids {c : ℂ} {T : ℂ → ℂ} {A : Set ℂ} {r : ℝ}
    (hT : AnalyticOnNhd ℂ T A) (hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ A)
    {L : ℝ} (hlev : ∀ θ : ℝ, greenFunctionDyn c (T (circleMap 0 r θ)) = L)
    {p : ℂ} (hp : greenFunctionDyn c p ≠ L) :
    (sectionLoop hT hcirc).Avoids p := by
  intro θ h
  apply hp
  rw [← hlev θ, ← h]
  rfl

/-- **Sublevel transport of the winding.**  If a loop runs at constant Green level `L > G_c(0)`,
its winding about any point of level `< L` equals its winding about `0`. -/
theorem windInt_eq_windInt_zero_of_level {c : ℂ} (ℓ : C1Loop) {L : ℝ}
    (h0 : greenFunctionDyn c 0 < L)
    (hlev : ∀ θ : ℝ, greenFunctionDyn c (ℓ.γ θ) = L)
    {p : ℂ} (hp : greenFunctionDyn c p < L) :
    windInt ℓ p = windInt ℓ 0 := by
  have hpre := (isConnected_green_sublevel c h0).isPreconnected
  have hSA : ∀ z ∈ {z : ℂ | greenFunctionDyn c z < L}, ℓ.Avoids z := by
    intro z hz θ h
    rw [mem_setOf_eq, ← h, hlev θ] at hz
    exact lt_irrefl _ hz
  exact windInt_eq_on_preconnected ℓ hpre hSA hp h0

/-- **The doubling identity.**  For `2π`-periodic `δ, δ'` with `δ` differentiable everywhere and
`δ` avoiding `a`, the winding integrand of `θ ↦ δ(2θ)` (with chain velocity `2·δ'(2θ)`) integrates
to twice the winding of `δ`. -/
theorem windInt_double {δ δ' : ℝ → ℂ} {a : ℂ}
    (hδcont : Continuous δ) (hδ'cont : Continuous δ')
    (hA : ∀ θ : ℝ, δ θ ≠ a)
    (hperδ : Function.Periodic δ (2 * Real.pi))
    (hperδ' : Function.Periodic δ' (2 * Real.pi)) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), (δ (2 * θ) - a)⁻¹ * (2 * δ' (2 * θ)))
      = 2 * ∫ θ in (0:ℝ)..(2 * Real.pi), (δ θ - a)⁻¹ * δ' θ := by
  set F : ℝ → ℂ := fun u => (δ u - a)⁻¹ * δ' u with hFdef
  have hFcont : Continuous F := by
    have hne : ∀ u : ℝ, δ u - a ≠ 0 := fun u => sub_ne_zero.mpr (hA u)
    exact ((hδcont.sub continuous_const).inv₀ hne).mul hδ'cont
  have hstep1 : (∫ θ in (0:ℝ)..(2 * Real.pi), (δ (2 * θ) - a)⁻¹ * (2 * δ' (2 * θ)))
      = 2 * ∫ θ in (0:ℝ)..(2 * Real.pi), F (2 * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    rw [hFdef]
    ring
  have hstep2 : (∫ θ in (0:ℝ)..(2 * Real.pi), F (2 * θ))
      = (2:ℝ)⁻¹ • ∫ u in (2*(0:ℝ))..(2*(2 * Real.pi)), F u :=
    intervalIntegral.integral_comp_mul_left F (by norm_num : (2:ℝ) ≠ 0)
  have hstep3 : (∫ u in (0:ℝ)..(2*(2 * Real.pi)), F u)
      = (∫ u in (0:ℝ)..(2 * Real.pi), F u) + ∫ u in (2 * Real.pi)..(2*(2 * Real.pi)), F u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hFcont.intervalIntegrable _ _) (hFcont.intervalIntegrable _ _)).symm
  have hstep4 : (∫ u in (2 * Real.pi)..(2*(2 * Real.pi)), F u)
      = ∫ u in (0:ℝ)..(2 * Real.pi), F u := by
    have h1 : (∫ u in (0:ℝ)..(2 * Real.pi), F (u + 2 * Real.pi))
        = ∫ u in ((0:ℝ) + 2 * Real.pi)..((2 * Real.pi) + 2 * Real.pi), F u :=
      intervalIntegral.integral_comp_add_right F (2 * Real.pi)
    have h2 : (∫ u in (0:ℝ)..(2 * Real.pi), F (u + 2 * Real.pi))
        = ∫ u in (0:ℝ)..(2 * Real.pi), F u := by
      apply intervalIntegral.integral_congr
      intro u _
      rw [hFdef]
      simp only
      rw [hperδ u, hperδ' u]
    have h3 : (∫ u in ((0:ℝ) + 2 * Real.pi)..((2 * Real.pi) + 2 * Real.pi), F u)
        = ∫ u in (2 * Real.pi)..(2*(2 * Real.pi)), F u := by
      congr 1 <;> ring
    rw [← h3, ← h1, h2]
  rw [hstep1, hstep2]
  rw [show (2:ℝ)*(0:ℝ) = (0:ℝ) from by ring]
  rw [hstep3, hstep4, Complex.real_smul]
  push_cast
  ring

end Bottcher
