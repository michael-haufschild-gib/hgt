import GaloisForLFunctions.HTGeometry.ShiftedDerivativeCoercivity

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

/-- **Coercivity gives a norm bound.**  If the quadratic form of a state against its image is at
least `c ‖u‖²`, the state is bounded by its image over `c`.  This is the step that turns a
numerical-range lower bound into weighted membership of a derivative. -/
theorem norm_le_of_coercive {c : ℝ} {u w : E} (h : c * ‖u‖ ^ 2 ≤ inner ℝ u w) :
    c * ‖u‖ ≤ ‖w‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hcs : inner ℝ u w ≤ ‖u‖ * ‖w‖ :=
      le_trans (le_abs_self _) (abs_real_inner_le_norm u w)
    nlinarith [h, hcs]

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

/-! ## The resolvent input, discharged

The scalar estimates above take `σ ‖Y‖ ≤ d ‖V‖ + ‖H‖` as an input.  That input is not an
assumption: it is the coercivity of the shifted derivative applied to the graph equation.  The
results below chain the two, so the state bound rests only on the flux equation itself.
-/

section FluxEquation

open MeasureTheory

/-- **The resolvent estimate on a solution of the flux equation.**  If `Y` solves
`(∂ − σ)Y = W` then `σ ‖Y‖₂ ≤ ‖W‖₂`.  Nothing is assumed about `W` beyond the equation. -/
theorem sigma_mul_l2_le_of_flux_equation {σ : ℝ} (hσ : 0 < σ) {Y W : ℝ → ℂ}
    (hdiff : Differentiable ℝ Y) (hcont : Continuous (deriv Y)) (hc : HasCompactSupport Y)
    (heq : ∀ x, deriv Y x - (σ : ℂ) * Y x = W x) :
    σ * Real.sqrt (∫ x, ‖Y x‖ ^ 2) ≤ Real.sqrt (∫ x, ‖W x‖ ^ 2) := by
  have hkey := abs_mul_sqrt_integral_normSq_le σ hdiff hcont hc
  rw [abs_of_pos hσ] at hkey
  have hcongr : (∫ x, ‖deriv Y x - (σ : ℂ) * Y x‖ ^ 2) = ∫ x, ‖W x‖ ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [heq x])
  rwa [hcongr] at hkey

/-- **The graph flux state bound with every input discharged.**  The only hypotheses left are the
flux equation, the coupling bound on the source, the coercivity estimate for the graph equation,
and the spectral gap.  The resolvent estimate `(13)` is no longer assumed — it is derived. -/
theorem graphFlux_state_bound_of_flux_equation {c d σ V G H : ℝ} (hσ : 0 < σ) {Y W : ℝ → ℂ}
    (hdiff : Differentiable ℝ Y) (hcont : Continuous (deriv Y)) (hc : HasCompactSupport Y)
    (heq : ∀ x, deriv Y x - (σ : ℂ) * Y x = W x)
    (hsrc : Real.sqrt (∫ x, ‖W x‖ ^ 2) ≤ d * V + H)
    (hcoup : c * V ≤ Real.sqrt (∫ x, ‖Y x‖ ^ 2) + G) (hgap : d / σ < c) :
    V ≤ (c - d / σ)⁻¹ * (G + σ⁻¹ * H) :=
  graphFlux_state_bound hσ hcoup
    ((sigma_mul_l2_le_of_flux_equation hσ hdiff hcont hc heq).trans hsrc) hgap

end FluxEquation

end GaloisForLFunctions.HTGeometry
