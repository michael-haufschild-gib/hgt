/-
# q62 — Brolin equidistribution: the unconditional Riesz identity for `gapAMu`

The GAP-A both-connected case (`c ∈ M`, positive-area `K_c`) needs
`IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c)` **unconditionally** — the tree currently has
it only under `volume(filledJulia c) = 0` (`isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null`).
This is Brolin/Lyubich equidistribution: the preimage measures converge to `(2π)⁻¹ Δ G_c`.

## Architecture (this file = the verified keystone; analytic core still to fill)

For `φ : C²` compact support, the finite pre-Brolin potential is
`gₙ(z) = −logPot(preBrolinMeasure c n) z = greenApprox c z n = (2ⁿ)⁻¹ log‖fⁿ(z)‖`.

```
∫ φ d(gapAMu) = limₖ ∫ φ d(preBrolinMeasure c (ψ k))       -- weak-* (limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin)
             = limₖ (2π)⁻¹ ∫ g_{ψ k} · Δφ                   -- per-level Riesz (isRieszMeasureOfSmooth_preBrolinMeasure)
             = (2π)⁻¹ ∫ G_c · Δφ                            -- THE ONE ANALYTIC CORE `hConv`
```

`isRieszMeasureOfSmooth_gapAMu_of_greenApprox_integral_tendsto` (below) discharges everything **except**
`hConv : ∫ g_{ψ k} · Δφ → ∫ G_c · Δφ`.  That convergence is Vitali's theorem applied to `{gₙ}`:
* **(P1)** `gₙ → G_c` a.e. — off `K_c` from the escape-rate limit; on `K_c` (`gₙ = (2ⁿ)⁻¹ log‖fⁿ‖ → 0`
  a.e.) via Borel–Cantelli on the tree's quadratic area formula.
* **(P2)** `{gₙ}` uniformly integrable on any ball — from a uniform `L²` bound
  `‖gₙ‖_{L²(B)} ≤ C_B` (Minkowski over the `2ⁿ`-term average of the log kernel).
mathlib's `tendstoInMeasure_iff_tendsto_Lp_finite` + `tendstoInMeasure_of_tendsto_ae` then give the
`L¹(B)` convergence, hence `hConv` (`Δφ` bounded, compactly supported).
-/
import GaloisForLFunctions.Bottcher.Brolin.RieszPerLevel
import GaloisForLFunctions.Bottcher.Brolin.GapAMuCore
import GaloisForLFunctions.Bottcher.Brolin.FiniteLimits

open MeasureTheory Complex Filter Topology CompactlySupported Laplacian InnerProductSpace
open scoped Laplacian

namespace Bottcher

noncomputable section

/-- **Brolin equidistribution keystone.**  The unconditional Riesz identity
`IsRieszMeasureOfSmooth (gapAMu c) G_c` follows from the single analytic convergence `hConv` — the
weak-`*` limit, the per-level Riesz identity, and uniqueness of limits do the rest.  `hConv` is the
Vitali `L¹` passage `∫ gₙ·Δφ → ∫ G_c·Δφ` (see the module docstring); everything else is discharged
here. -/
theorem isRieszMeasureOfSmooth_gapAMu_of_greenApprox_integral_tendsto {c : ℂ}
    (hConv : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      Tendsto (fun k => ∫ z, greenApprox c z (brolinLimitSubsequence c k) * Δ φ z)
        atTop (𝓝 (∫ z, greenFunctionDyn c z * Δ φ z))) :
    IsRieszMeasureOfSmooth (gapAMu c) (greenFunctionDyn c) := by
  intro φ hφ hφc
  let φcc : CompactlySupportedContinuousMap ℂ ℝ := ⟨⟨φ, hφ.continuous⟩, hφc⟩
  have hgap : gapAMu c = limitingBrolinMeasure c := by rw [gapAMu_eq_brolinMu, brolinMu]
  have hweak : Tendsto (fun k => ∫ z, φ z ∂preBrolinMeasure c (brolinLimitSubsequence c k)) atTop
      (𝓝 (∫ z, φ z ∂gapAMu c)) := by
    have h := limitingBrolinMeasure_isWeakSubseqLimitOfPreBrolin c φcc
    rw [hgap]; exact h
  have hlevel : (fun k => ∫ z, φ z ∂preBrolinMeasure c (brolinLimitSubsequence c k)) =
      (fun k => (2 * Real.pi)⁻¹ * ∫ z, greenApprox c z (brolinLimitSubsequence c k) * Δ φ z) := by
    funext k
    exact isRieszMeasureOfSmooth_preBrolinMeasure c (brolinLimitSubsequence c k) φ hφ hφc
  rw [hlevel] at hweak
  have hConv' : Tendsto
      (fun k => (2 * Real.pi)⁻¹ * ∫ z, greenApprox c z (brolinLimitSubsequence c k) * Δ φ z) atTop
      (𝓝 ((2 * Real.pi)⁻¹ * ∫ z, greenFunctionDyn c z * Δ φ z)) :=
    (hConv φ hφ hφc).const_mul _
  exact tendsto_nhds_unique hweak hConv'

end

end Bottcher
