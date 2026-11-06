import GaloisForLFunctions.BlackHoleRingdown.TheEisensteinWavePacket
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBackgroundMetricTwoJet

/-!
# The wave packet on the metric of the modular horizon

The Laplace–Beltrami operator `|g|^{-1/2} ∂ᵢ(|g|^{1/2} gⁱⁱ ∂ᵢ F)` of the massless topological black hole
`-(r²-1) dt² + dr²/(r²-1) + r²(dx² + dy²)/y²` is written here through the metric itself: its inverse and
its determinant. It agrees with the explicit operator used by the radial reduction. The scalar curvature
of the same metric is `R = -12`, so the conformal coupling `-R/6` equals `+2`. The Neumann and Dirichlet
lifts of the Eisenstein wave packet therefore solve the conformally coupled wave equation of the metric
on the exterior, and both are invariant under `SL₂(ℤ)`, so they live on the horizon `PSL₂(ℤ)\ℍ`.
-/

open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower

/-- The diagonal entries of the inverse metric on the real chart. -/
def inverseMetric (r y : ℝ) (i : Fin 4) : ℂ := (D4BMBackground.metric (r : ℂ) (y : ℂ))⁻¹ i i

/-- The volume density `r²/y²`. -/
def volumeDensity (r y : ℝ) : ℝ := r ^ 2 / y ^ 2

theorem sq_sub_one_ne_zero {r : ℝ} (hr : 1 < r) : (r : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
  have h : r ^ 2 - 1 ≠ 0 := by nlinarith
  exact_mod_cast h

/-- The density squares to `-det g`. -/
theorem volumeDensity_sq {r y : ℝ} (hr : 1 < r) (hy : 0 < y) :
    ((volumeDensity r y : ℝ) : ℂ) ^ 2 = -(D4BMBackground.metric (r : ℂ) (y : ℂ)).det := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [D4BMBackground.metric_det _ _ (sq_sub_one_ne_zero hr), volumeDensity]
  push_cast
  field_simp

/-- The inverse metric, entry by entry. -/
theorem inverseMetric_eq {r y : ℝ} (hr : 1 < r) (hy : y ≠ 0) :
    inverseMetric r y 0 = ((-(r ^ 2 - 1)⁻¹ : ℝ) : ℂ) ∧ inverseMetric r y 1 = ((r ^ 2 - 1 : ℝ) : ℂ) ∧
      inverseMetric r y 2 = ((y ^ 2 / r ^ 2 : ℝ) : ℂ) ∧
      inverseMetric r y 3 = ((y ^ 2 / r ^ 2 : ℝ) : ℂ) := by
  have hrC : (r : ℂ) ≠ 0 := by
    have : r ≠ 0 := by linarith
    exact_mod_cast this
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hd := D4BMBackground.metric_inverse (r : ℂ) (y : ℂ) hrC hyC (sq_sub_one_ne_zero hr)
  simp only [inverseMetric, hd, Matrix.diagonal_apply_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp [div_eq_mul_inv]
  · simp [div_eq_mul_inv]

/-- The Laplace–Beltrami operator of the metric in the chart `(t, r, x, y)`. -/
def metricWaveOperator (F : ℝ → ℝ → ℝ → ℝ → ℂ) (t r x y : ℝ) : ℂ :=
  ((volumeDensity r y : ℝ) : ℂ)⁻¹ *
    (deriv (fun s => ((volumeDensity r y : ℝ) : ℂ) * inverseMetric r y 0 *
        deriv (fun s' => F s' r x y) s) t +
      deriv (fun ρ => ((volumeDensity ρ y : ℝ) : ℂ) * inverseMetric ρ y 1 *
        deriv (fun ρ' => F t ρ' x y) ρ) r +
      deriv (fun ξ => ((volumeDensity r y : ℝ) : ℂ) * inverseMetric r y 2 *
        deriv (fun ξ' => F t r ξ' y) ξ) x +
      deriv (fun η => ((volumeDensity r η : ℝ) : ℂ) * inverseMetric r η 3 *
        deriv (fun η' => F t r x η') η) y)

/-- **The operator of the metric is the explicit operator of the radial reduction.** -/
theorem metricWaveOperator_eq (F : ℝ → ℝ → ℝ → ℝ → ℂ) {t r x y : ℝ} (hr : 1 < r) (hy : 0 < y) :
    metricWaveOperator F t r x y = blackHoleWaveOperator F t r x y := by
  obtain ⟨h0, -, h2, -⟩ := inverseMetric_eq hr hy.ne'
  have hpre : ((volumeDensity r y : ℝ) : ℂ)⁻¹ = ((y ^ 2 / r ^ 2 : ℝ) : ℂ) := by
    rw [volumeDensity, ← Complex.ofReal_inv, inv_div]
  have hT : (fun s => ((volumeDensity r y : ℝ) : ℂ) * inverseMetric r y 0 *
      deriv (fun s' => F s' r x y) s) =
      fun s => ((r ^ 2 / y ^ 2 * (-(r ^ 2 - 1)⁻¹) : ℝ) : ℂ) * deriv (fun s' => F s' r x y) s := by
    funext s
    rw [h0, volumeDensity]
    push_cast
    rfl
  have hX : (fun ξ => ((volumeDensity r y : ℝ) : ℂ) * inverseMetric r y 2 *
      deriv (fun ξ' => F t r ξ' y) ξ) =
      fun ξ => ((r ^ 2 / y ^ 2 * (y ^ 2 / r ^ 2) : ℝ) : ℂ) * deriv (fun ξ' => F t r ξ' y) ξ := by
    funext ξ
    rw [h2, volumeDensity]
    push_cast
    rfl
  have hR : (fun ρ => ((volumeDensity ρ y : ℝ) : ℂ) * inverseMetric ρ y 1 *
      deriv (fun ρ' => F t ρ' x y) ρ) =ᶠ[𝓝 r]
      fun ρ => ((ρ ^ 2 / y ^ 2 * (ρ ^ 2 - 1) : ℝ) : ℂ) * deriv (fun ρ' => F t ρ' x y) ρ := by
    filter_upwards [lt_mem_nhds hr] with ρ hρ
    rw [(inverseMetric_eq hρ hy.ne').2.1, volumeDensity]
    push_cast
    rfl
  have hY : (fun η => ((volumeDensity r η : ℝ) : ℂ) * inverseMetric r η 3 *
      deriv (fun η' => F t r x η') η) =ᶠ[𝓝 y]
      fun η => ((r ^ 2 / η ^ 2 * (η ^ 2 / r ^ 2) : ℝ) : ℂ) * deriv (fun η' => F t r x η') η := by
    filter_upwards [lt_mem_nhds hy] with η hη
    rw [(inverseMetric_eq hr hη.ne').2.2.2, volumeDensity]
    push_cast
    rfl
  rw [metricWaveOperator, blackHoleWaveOperator, hpre, hT, hX, hR.deriv_eq, hY.deriv_eq]

/-- **The conformal coupling is `+2`.**  The metric has `R = -12`, so `-R/6 = 2`. -/
theorem conformalCoupling_eq {r y : ℝ} (hr : 1 < r) (hy : 0 < y) :
    -(1 / 6 : ℂ) * (D4BMBackground.jet (r : ℂ) (y : ℂ)).scalar = 2 := by
  have hrC : (r : ℂ) ≠ 0 := by
    have : r ≠ 0 := by linarith
    exact_mod_cast this
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [D4BMBackground.jet_scalar _ _ hrC hyC (sq_sub_one_ne_zero hr)]
  norm_num

/-- **The Neumann field solves the conformally coupled wave equation of the metric.** -/
theorem neumannField_metric_wave {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {t r x y : ℝ} (hr : 1 < r)
    (hy : 0 < y) :
    metricWaveOperator (conformalScalar (neumannProfile ε ξ₀)) t r x y -
      (1 / 6 : ℂ) * (D4BMBackground.jet (r : ℂ) (y : ℂ)).scalar *
        conformalScalar (neumannProfile ε ξ₀) t r x y = 0 := by
  have h := neumannField_wave (t := t) (x := x) hε ξ₀ hr hy
  have hc := conformalCoupling_eq hr hy
  rw [metricWaveOperator_eq _ hr hy]
  linear_combination h + conformalScalar (neumannProfile ε ξ₀) t r x y * hc

/-- **The Dirichlet field solves the conformally coupled wave equation of the metric.** -/
theorem dirichletField_metric_wave {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {t r x y : ℝ} (hr : 1 < r)
    (hy : 0 < y) :
    metricWaveOperator (conformalScalar (dirichletProfile ε ξ₀)) t r x y -
      (1 / 6 : ℂ) * (D4BMBackground.jet (r : ℂ) (y : ℂ)).scalar *
        conformalScalar (dirichletProfile ε ξ₀) t r x y = 0 := by
  have h := dirichletField_wave (t := t) (x := x) hε ξ₀ hr hy
  have hc := conformalCoupling_eq hr hy
  rw [metricWaveOperator_eq _ hr hy]
  linear_combination h + conformalScalar (dirichletProfile ε ξ₀) t r x y * hc

/-! ### Descent to the modular horizon -/

/-- **The Neumann field descends to `PSL₂(ℤ)\ℍ`.** -/
theorem neumannField_smul (ε ξ₀ t r : ℝ) (γ : SL(2, ℤ)) (z : ℍ) :
    conformalScalar (neumannProfile ε ξ₀) t r (γ • z : ℍ).re (γ • z : ℍ).im =
      conformalScalar (neumannProfile ε ξ₀) t r z.re z.im := by
  simp only [conformalScalar, neumannProfile, neumannLift, dampedProfile]
  rw [wavePacket_smul]

/-- **The Dirichlet field descends to `PSL₂(ℤ)\ℍ`.** -/
theorem dirichletField_smul (ε ξ₀ t r : ℝ) (γ : SL(2, ℤ)) (z : ℍ) :
    conformalScalar (dirichletProfile ε ξ₀) t r (γ • z : ℍ).re (γ • z : ℍ).im =
      conformalScalar (dirichletProfile ε ξ₀) t r z.re z.im := by
  simp only [conformalScalar, dirichletProfile, dirichletLift, dampedProfile]
  rw [wavePacket_smul]

end GaloisForLFunctions.BlackHoleRingdown

end
