import GaloisForLFunctions.RHTower.Sieve.RouteTZetaLandauGrowth
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleLogDeriv

/-!
# Route-T de la Vallée Poussin inequality

All analytic growth hypotheses of the general DLVP theorem are discharged by the Route-T unit-band
rectangle.  Only explicit scalar optimization remains.
-/

namespace RHTower.Sieve

open Complex Metric

noncomputable section

/-- **Route-T DLVP inequality.**  A zero in the retained half-disc forces this explicit scalar
inequality, with radius and growth bound selected canonically from its height. -/
theorem routeT_dlvp_inequality
    {β γ δ A : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hγ : 100000 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ (10 : ℕ) ≤ routeTBinaryHeight γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hβ1 : β ≤ 1)
    (hclose : 1 + δ - β ≤ routeTLandauRadius γ / 4)
    (hzero : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    4 / (1 + δ - β) ≤ 3 / δ + 3 * A +
      160 / routeTLandauRadius γ *
        (5 / 4 * Real.log (routeTLandauPhi γ) +
          3 / 4 * Real.log (1 + 1 / δ) + 6) := by
  have hγ3 : 3 ≤ γ := by linarith
  have hrad0 := routeTLandauRadius_pos γ
  have hradHalf := routeTLandauRadius_lt_half γ
  have hΦ0 := routeTLandauPhi_one_le γ
  have hmain := dlvp_inequality_of_bound
    (β := β) (γ := γ) (δ := δ) (A := A)
    (R := routeTLandauRadius γ / 2) (R₀ := routeTLandauRadius γ)
    (Φ := routeTLandauPhi γ) hA hγ3 hδ0 hδ
    (by positivity) (by linarith) (by linarith)
    (fun w hw => routeT_landau_disc_growth_first hγ hlarge hδ0 hδ hw)
    (fun w hw => routeT_landau_disc_growth_second hγ hlarge hδ0 hδ hw)
    (routeT_landau_growth_fourth hγ hlarge hδ0 hδ).le hΦ0 hβ1
    (by linarith [hclose]) hzero
  have hrw : (80 : ℝ) / (routeTLandauRadius γ / 2) =
      160 / routeTLandauRadius γ := by
    field_simp [ne_of_gt hrad0]
    norm_num
  rw [hrw] at hmain
  exact hmain

/-- Contrapositive form consumed by zero-free optimization. -/
theorem riemannZeta_ne_zero_routeT_of_dlvp_lt
    {β γ δ A : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hγ : 100000 ≤ γ)
    (hlarge : routeTBandDepthRootThreshold ^ (10 : ℕ) ≤ routeTBinaryHeight γ)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hβ1 : β ≤ 1)
    (hclose : 1 + δ - β ≤ routeTLandauRadius γ / 4)
    (hfail : 3 / δ + 3 * A +
        160 / routeTLandauRadius γ *
          (5 / 4 * Real.log (routeTLandauPhi γ) +
            3 / 4 * Real.log (1 + 1 / δ) + 6)
      < 4 / (1 + δ - β)) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  exact absurd
    (routeT_dlvp_inequality hA hγ hlarge hδ0 hδ hβ1 hclose hzero)
    (not_le.2 hfail)

end

end RHTower.Sieve
