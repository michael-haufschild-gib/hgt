import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaWeakDomainUpgrade
import GaloisForLFunctions.RHTower.WallFirstBoundarySquareIntegrable
import GaloisForLFunctions.HTGeometry.LogChartEnergyExtended

/-!
# `(7)` and `(8)`: the weighted derivative becomes physical `H¹`

The coercive weighted-tail theorem produces `u = V′ − σV` in `L²`, where `V = e^{σL}W`.  In the
physical variable that says `e^{σL}W′ ∈ L²`, and the chart identity converts a weighted log
derivative with exponent above `1/2` into a spatial `L²` derivative, because the chart's own weight
is `e^{L}` and `e^{L} ≤ e^{2σL}` on the terminal ray exactly when `2σ ≥ 1`.

So the two conclusions of the scale-gap theorem come out of the same object: `(7)` is the weighted
statement and `(8)` is its image under the chart.
-/

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **`(8)` from `(18)`.**  A weighted log derivative with exponent above `1/2` gives a spatial `L²`
derivative on the punctured interval. -/
theorem lintegral_sq_spatial_ne_top_of_weightedDeriv {σ L₀ : ℝ} {u : ℝ → ℝ}
    (hσ : 1 / 2 < σ) (hL₀ : 0 ≤ L₀) (hu2 : MemLp u 2 (volume : Measure ℝ)) :
    (∫⁻ r in Ioo (0 : ℝ) (Real.exp (-L₀)),
        ‖(-r⁻¹) • (Real.exp (-(σ * (-Real.log r))) * u (-Real.log r))‖ₑ ^ 2) ≠ ⊤ := by
  refine lintegral_sq_spatial_ne_top_of_weighted (F' := fun L : ℝ => Real.exp (-(σ * L)) * u L)
    hσ hL₀ ?_
  have hcongr : (∫⁻ L in Ioi L₀, ‖Real.exp (σ * L) • (Real.exp (-(σ * L)) * u L)‖ₑ ^ 2)
      = ∫⁻ L in Ioi L₀, ‖u L‖ₑ ^ 2 := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun L _ => ?_
    congr 2
    rw [smul_eq_mul, ← mul_assoc, ← Real.exp_add]
    norm_num
  rw [hcongr]
  have hfin : (∫⁻ L : ℝ, ‖u L‖ₑ ^ 2) ≠ ⊤ := by
    have hsq : Integrable (fun L : ℝ => ‖u L‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hu2.aestronglyMeasurable).mp hu2
    rw [lintegral_enorm_sq_eq_ofReal_integral hsq]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral _ _)

/-- **`(7)` and `(8)` together.**  From the tested weak equation on the coercive budget: the weighted
derivative is `L²`, the profile is weakly differentiable, and the transported profile has a spatial
`L²` derivative on the punctured interval. -/
theorem scalarAnalyticForcing_physical_H1 {σ τ L₀ : ℝ} {V G : ℝ → ℝ}
    (heq : SuzukiGammaTestedEquation σ τ V G)
    (hVmm : Measurable V) (hV2 : Integrable fun t => V t ^ 2)
    (hGmm : Measurable G) (hG2 : Integrable fun t => G t ^ 2)
    (hsupp : ∀ t : ℝ, t < L₀ → V t = 0)
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hL₀ : 0 ≤ L₀)
    (hbudget : suzukiGammaShiftKappa σ + |τ| < 2 * L₀) :
    ∃ u : ℝ → ℝ, MemLp u 2 (volume : Measure ℝ)
      ∧ (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ t, u t * φ t) = -(∫ t, V t * deriv φ t) - σ * ∫ t, V t * φ t)
      ∧ MemLp (fun t => σ * V t + u t) 2 (volume : Measure ℝ)
      ∧ (∫⁻ r in Ioo (0 : ℝ) (Real.exp (-L₀)),
          ‖(-r⁻¹) • (Real.exp (-(σ * (-Real.log r))) * u (-Real.log r))‖ₑ ^ 2) ≠ ⊤ := by
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  obtain ⟨u, hu2, hu⟩ := suzukiGamma_weakDomain_upgrade heq hVmm hV2 hGmm hG2 hsupp hσ0 hσ1 hbudget
  have hVmem : MemLp V 2 (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq hVmm.aestronglyMeasurable).mpr hV2
  refine ⟨u, hu2, hu, (hVmem.const_mul σ).add hu2, ?_⟩
  exact lintegral_sq_spatial_ne_top_of_weightedDeriv hσ hL₀ hu2


/-- The transported profile's own `L²` part on the punctured interval: a bounded profile has finite
mass there because the interval has finite length. -/
theorem lintegral_sq_logTransport_ne_top {W : ℝ → ℝ} {B L₀ : ℝ} (hB : ∀ x, |W x| ≤ B) :
    (∫⁻ r in Ioo (0 : ℝ) (Real.exp (-L₀)), ‖W (-Real.log r)‖ₑ ^ 2) ≠ ⊤ := by
  have hB0 : (0 : ℝ) ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hbd : ∀ r ∈ Ioo (0 : ℝ) (Real.exp (-L₀)), ‖W (-Real.log r)‖ₑ ^ 2
      ≤ ENNReal.ofReal (B ^ 2) := by
    intro r _
    have h1 : ‖W (-Real.log r)‖ₑ ≤ ENNReal.ofReal B := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hB _)
    calc ‖W (-Real.log r)‖ₑ ^ 2 ≤ ENNReal.ofReal B ^ 2 := pow_le_pow_left' h1 2
      _ = ENNReal.ofReal (B ^ 2) := (ENNReal.ofReal_pow hB0 2).symm
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioo hbd)
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Real.volume_Ioo])

end GaloisForLFunctions.RHTower
