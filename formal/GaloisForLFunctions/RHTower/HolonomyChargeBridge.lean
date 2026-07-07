/-
# The order–spectral seam: the deck charge is the circle-trace holonomy

The base deck charge `carrierCharge f 1 ρ = (−1)^{ord}` is read from the vanishing order — a
constraint, no path and no integral.  The root-trace holonomy reads the *same* number as the
endpoint ratio of a continuous square-root trace transported once around a circle enclosing
ρ.  This file welds them: for any carrier with an isolated zero, every such trace returns
multiplied by `carrierCharge f 1 ρ`.

This is the exact seam between the two readings.  The identity uses the circle only as a
*path* (`circleMap`); it integrates nothing.  The spectral reading of the same holonomy
(`doubledTrace_pairing`) adds a circle integral, turning the parity into positivity of a
boundary L² pairing.  So `carrierCharge` (pure order) → this holonomy (circle path, no
integral) → the spectral functional (circle integral) is a graded ascent from constraint to
flow, and the charge sits at the constraint end.
-/
import GaloisForLFunctions.RHTower.CarrierDeckCharge
import GaloisForLFunctions.RHTower.RootTraceHolonomy

namespace RHTower

open Complex Metric Set

/-- **The holonomy of a circle trace is the base deck charge.**  For a carrier `f` analytic on
`ball ρ R` with ρ its only zero there, every continuous square-root trace `U` along the
interior circle of radius `r` returns with `U(3π/2) = carrierCharge f 1 ρ · U(−π/2)`: the
endpoint holonomy is exactly the level-`2` deck charge `(−1)^{ord}`.  The circle enters only
as a path. -/
theorem trace_holonomy_eq_carrierCharge_one {f : ℂ → ℂ} {ρ : ℂ} {r₀ r R : ℝ}
    (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → f z ≠ 0)
    {G₁ G₂ : ℂ → ℂ}
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA ρ r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA ρ r₀ R))
    (hpG₁ : ∀ z ∈ chartRA ρ r₀ R, G₁ z ^ 2 = f z)
    (hpG₂ : ∀ z ∈ chartLA ρ r₀ R, G₂ z ^ 2 = f z)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ 2 = f (circleMap ρ r θ)) :
    U (3 * Real.pi / 2) = carrierCharge f 1 ρ * U (-(Real.pi / 2)) := by
  have hR : 0 < R := lt_of_le_of_lt h0 (lt_trans hr₀ hrR)
  have hfin : analyticOrderAt f ρ ≠ ⊤ := by
    intro htop
    have hev0 : f =ᶠ[nhds ρ] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have hzero : Set.EqOn f 0 (ball ρ R) :=
      hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball ρ R).isPreconnected (mem_ball_self hR) hev0
    set z₀ : ℂ := ρ + ((r : ℝ) : ℂ) with hz₀def
    have hrpos : 0 < r := lt_of_le_of_lt h0 hr₀
    have hz₀sub : z₀ - ρ = ((r : ℝ) : ℂ) := by rw [hz₀def]; ring
    have hz₀ball : z₀ ∈ ball ρ R := by
      rw [mem_ball, Complex.dist_eq, hz₀sub, Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      exact hrR
    have hz₀ne : z₀ ≠ ρ := by
      intro h
      rw [← sub_eq_zero, hz₀sub] at h
      exact hrpos.ne' (by exact_mod_cast h)
    exact hiso z₀ hz₀ball hz₀ne (hzero hz₀ball)
  set m : ℕ := (analyticOrderAt f ρ).toNat with hmdef
  have hm : analyticOrderAt f ρ = (m : ℕ∞) := (ENat.coe_toNat hfin).symm
  have h := trace_holonomy_isolated_zero h0 hr₀ hrR hf hiso hm hG₁ hG₂ hpG₁ hpG₂ hUc hUsq
  rw [carrierCharge_one_eq_neg_one_pow, ← hmdef]
  exact h

end RHTower
