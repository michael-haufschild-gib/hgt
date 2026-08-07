import Mathlib

/-!
# Stability of a first-order graph flux system

A weighted flux system couples a coercive graph equation to a resolvent estimate:

`c ‖V‖ ≤ ‖Y‖ + ‖G‖`   and   `σ ‖Y‖ ≤ d ‖V‖ + ‖H‖`.

Whenever the coercivity beats the coupling, `c > d/σ`, the two together bound both unknowns by the
data alone.  The argument is scalar — only norms enter — which is exactly why no symmetry or
normality of the coupling operator is needed.

The numerical-range input for the coupling is also here: for a bounded operator the real part of
`⟪-B v, v⟫` is at least `-‖B‖ ‖v‖²`, with no self-adjointness.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ## The scalar stability estimate -/

/-- **Stability of the graph flux system.**  Coercivity beating the coupling bounds the state by
the data. -/
theorem graphFlux_state_bound {c d σ V Y G H : ℝ} (hσ : 0 < σ)
    (hcoup : c * V ≤ Y + G) (hres : σ * Y ≤ d * V + H) (hgap : d / σ < c) :
    V ≤ (c - d / σ)⁻¹ * (G + σ⁻¹ * H) := by
  have hgap' : 0 < c - d / σ := by linarith
  have hY : Y ≤ (d * V + H) / σ := by
    rw [le_div_iff₀ hσ]
    linarith
  have hstep : (c - d / σ) * V ≤ G + σ⁻¹ * H := by
    have h1 : c * V ≤ (d * V + H) / σ + G := by linarith
    have h2 : (d * V + H) / σ = d / σ * V + σ⁻¹ * H := by
      field_simp
    rw [h2] at h1
    linarith
  rw [← le_div_iff₀' hgap'] at hstep
  calc V ≤ (G + σ⁻¹ * H) / (c - d / σ) := hstep
    _ = (c - d / σ)⁻¹ * (G + σ⁻¹ * H) := by rw [div_eq_inv_mul]

/-- **Stability of the flux.**  The flux is bounded by the state and the data. -/
theorem graphFlux_flux_bound {d σ V Y H : ℝ} (hσ : 0 < σ)
    (hres : σ * Y ≤ d * V + H) :
    Y ≤ σ⁻¹ * (d * V + H) := by
  rw [← le_div_iff₀' hσ] at hres
  calc Y ≤ (d * V + H) / σ := hres
    _ = σ⁻¹ * (d * V + H) := by rw [div_eq_inv_mul]

/-! ## The nonnormal numerical-range bound -/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **No symmetry is needed.**  For a bounded operator the real part of `⟪-B v, v⟫` is at least
`-‖B‖ ‖v‖²`, by Cauchy–Schwarz alone. -/
theorem neg_norm_mul_normSq_le_inner_neg_apply (B : E →L[ℝ] E) (v : E) :
    -(‖B‖ * ‖v‖ ^ 2) ≤ inner ℝ (-(B v)) v := by
  have hcs : |inner ℝ (B v) v| ≤ ‖B v‖ * ‖v‖ := abs_real_inner_le_norm _ _
  have hop : ‖B v‖ ≤ ‖B‖ * ‖v‖ := B.le_opNorm v
  have hv : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
  have habs := abs_le.mp hcs
  rw [inner_neg_left]
  nlinarith [habs.2, habs.1, hop, hv]

end

end GaloisForLFunctions.HTGeometry
