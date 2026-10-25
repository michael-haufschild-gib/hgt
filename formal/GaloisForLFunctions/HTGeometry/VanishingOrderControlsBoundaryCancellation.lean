import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Vanishing order controls boundary cancellation

Factoring the two finite analytic orders reduces a boundary identity to a
nonzero leading factor times a continuous boundary value. Growth smaller
than a simple pole cannot compensate for a positive loss of vanishing order.
-/

section

noncomputable section
set_option autoImplicit false
open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

/-- A boundary factor with less vanishing order cannot cancel growth smaller than a simple pole. -/
theorem eq_zero_of_boundary_order_loss
    {A B Φ K : ℂ → ℂ} {s₀ : ℂ}
    (hA : AnalyticAt ℂ A s₀) (hB : AnalyticAt ℂ B s₀)
    (hAfin : analyticOrderAt A s₀ ≠ ⊤)
    (hloss : analyticOrderAt B s₀ < analyticOrderAt A s₀)
    (hΦ : Tendsto (fun u : ℝ => (u : ℂ) * Φ (s₀ + u)) (𝓝[>] 0) (𝓝 0))
    (hK : Tendsto (fun u : ℝ => K (s₀ + u)) (𝓝[>] 0) (𝓝 (K s₀)))
    (hid : ∀ᶠ u : ℝ in 𝓝[>] 0, A (s₀ + u) * Φ (s₀ + u) =
      B (s₀ + u) * K (s₀ + u)) : K s₀ = 0 := by
  have hBfin : analyticOrderAt B s₀ ≠ ⊤ := by
    intro h
    rw [h] at hloss
    exact not_lt_of_ge le_top hloss
  let a := (analyticOrderAt A s₀).toNat
  let b := (analyticOrderAt B s₀).toNat
  have ha : (a : ℕ∞) = analyticOrderAt A s₀ := ENat.coe_toNat hAfin
  have hb : (b : ℕ∞) = analyticOrderAt B s₀ := ENat.coe_toNat hBfin
  have hba : b < a := by rw [← ha, ← hb] at hloss; exact_mod_cast hloss
  obtain ⟨g, hg, _, hAg⟩ := hA.analyticOrderAt_eq_natCast.mp ha.symm
  obtain ⟨h, hh, hh0, hBh⟩ := hB.analyticOrderAt_eq_natCast.mp hb.symm
  let d := a - b - 1
  have had : a = b + d + 1 := by omega
  have hcurve : Tendsto (fun u : ℝ => s₀ + (u : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
    have hc : Continuous (fun u : ℝ => s₀ + (u : ℂ)) := by fun_prop
    have hc0 : ContinuousAt (fun u : ℝ => s₀ + (u : ℂ)) 0 := hc.continuousAt
    have ht := hc0.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    simpa only [ofReal_zero, add_zero] using ht
  have hu : Tendsto (fun u : ℝ => (u : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    change Tendsto Complex.ofReal (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ))
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hhead := (hu.pow d).mul (hg.continuousAt.tendsto.comp hcurve)
  have hleft := hhead.mul hΦ
  rw [mul_zero] at hleft
  have hright := (hh.continuousAt.tendsto.comp hcurve).mul hK
  have heq : (fun u : ℝ => ((u : ℂ) ^ d * g (s₀ + u)) * ((u : ℂ) * Φ (s₀ + u)))
      =ᶠ[𝓝[>] 0] fun u : ℝ => h (s₀ + u) * K (s₀ + u) := by
    filter_upwards [self_mem_nhdsWithin, hcurve.eventually hAg,
      hcurve.eventually hBh, hid] with u hu0 hAg' hBh' hid'
    have hune : (u : ℂ) ≠ 0 := by exact_mod_cast (show 0 < u from hu0).ne'
    simp only [add_sub_cancel_left, smul_eq_mul] at hAg' hBh'
    apply mul_left_cancel₀ (pow_ne_zero b hune)
    calc
      (u : ℂ) ^ b * (((u : ℂ) ^ d * g (s₀ + u)) * ((u : ℂ) * Φ (s₀ + u))) =
          (u : ℂ) ^ a * g (s₀ + u) * Φ (s₀ + u) := by
        rw [had, pow_add, pow_add, pow_one]
        ring
      _ = A (s₀ + u) * Φ (s₀ + u) := by rw [hAg']
      _ = B (s₀ + u) * K (s₀ + u) := hid'
      _ = (u : ℂ) ^ b * (h (s₀ + u) * K (s₀ + u)) := by rw [hBh']; ring
  have hz : h s₀ * K s₀ = 0 := (tendsto_nhds_unique (hleft.congr' heq) hright).symm
  exact (mul_eq_zero.mp hz).resolve_left hh0

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.eq_zero_of_boundary_order_loss
end
end
