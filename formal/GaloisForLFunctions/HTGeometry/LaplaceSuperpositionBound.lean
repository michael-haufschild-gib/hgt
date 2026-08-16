import GaloisForLFunctions.HTGeometry.MinkowskiIntegralInequality
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponentially decaying slices sum to a finite operator bound

A profile written as a superposition over a Laplace parameter, whose slice `L²` norms decay like
`K e^{-ρs}`, has `L²` norm at most `K/ρ`.  Minkowski's integral inequality reduces this to the
scalar mass of the slice bound, and the exponential integral evaluates it.

This is the quantitative form of the step that turns the resolvent's Laplace representation into an
operator bound: the shift `L` and the numerical floor of the generator add, so the decay rate of the
slices is the *sum* of the two, and the resulting constant is the reciprocal of that sum.  A shift
that grows with the block index therefore buys a uniformly bounded constant, which is exactly why
the block estimate is independent of the block.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The exponential mass on the ray. -/
theorem lintegral_exp_decay_Ioi {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (K * Real.exp (-ρ * s)))
      = ENNReal.ofReal (K / ρ) := by
  have hint : IntegrableOn (fun s : ℝ => K * Real.exp (-ρ * s)) (Ioi (0 : ℝ)) volume :=
    (exp_neg_integrableOn_Ioi 0 hρ).const_mul K
  have hnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ K * Real.exp (-ρ * s) := by
    filter_upwards with s
    positivity
  have hval : (∫ s in Ioi (0 : ℝ), K * Real.exp (-ρ * s)) = K / ρ := by
    have hderiv : ∀ s ∈ Ioi (0 : ℝ),
        HasDerivAt (fun r : ℝ => -(K / ρ) * Real.exp (-ρ * r))
          (K * Real.exp (-ρ * s)) s := by
      intro s _
      have h1 : HasDerivAt (fun r : ℝ => -ρ * r) (-ρ) s := by
        simpa using (hasDerivAt_id s).const_mul (-ρ)
      have hexp : HasDerivAt (fun r : ℝ => Real.exp (-ρ * r))
          (Real.exp (-ρ * s) * (-ρ)) s := by
        simpa [mul_comm] using h1.exp
      have hbase := hexp.const_mul (-(K / ρ))
      refine hbase.congr_deriv ?_
      field_simp
    have hcont : ContinuousWithinAt (fun r : ℝ => -(K / ρ) * Real.exp (-ρ * r))
        (Ici (0 : ℝ)) 0 := by
      refine Continuous.continuousWithinAt ?_
      fun_prop
    have htend : Tendsto (fun r : ℝ => -(K / ρ) * Real.exp (-ρ * r)) atTop (𝓝 0) := by
      have hinner : Tendsto (fun r : ℝ => -ρ * r) atTop atBot := by
        have h0 : Tendsto (fun r : ℝ => ρ * r) atTop atTop :=
          Tendsto.const_mul_atTop hρ tendsto_id
        have h1 := tendsto_neg_atTop_atBot.comp h0
        refine h1.congr fun r => ?_
        simp [neg_mul]
      have hexp0 : Tendsto (fun r : ℝ => Real.exp (-ρ * r)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp hinner
      simpa using hexp0.const_mul (-(K / ρ))
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
    rw [hFTC]
    simp
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

variable {Y : Type*} [NormedAddCommGroup Y]

/-- **`(22)`: the Laplace superposition bound.**  Slice norms decaying at rate `ρ` give the profile
the `L²` bound `K/ρ`. -/
theorem lintegral_sq_laplaceSuperposition_le {Φ : ℝ → Y} {Ψ : ℝ → ℝ → Y} {ρ K : ℝ}
    (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hmeas : Measurable (Function.uncurry fun x s => ‖Ψ x s‖ₑ))
    (hΦ : ∀ x, ‖Φ x‖ₑ ≤ ∫⁻ s in Ioi (0 : ℝ), ‖Ψ x s‖ₑ)
    (hslice : ∀ s, (∫⁻ x, ‖Ψ x s‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (K * Real.exp (-ρ * s))) :
    (∫⁻ x, ‖Φ x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (K / ρ) := by
  have hbase := lintegral_sq_superposition_le (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
    (Φ := Φ) (Ψ := Ψ) (w := fun s => ENNReal.ofReal (K * Real.exp (-ρ * s)))
    hmeas hΦ hslice
  rwa [lintegral_exp_decay_Ioi hK hρ] at hbase

/-- **`(22)` with the slice bound required only on the ray.**  The slices at nonpositive parameter
are never seen by the superposition, so no bound is needed there. -/
theorem lintegral_sq_laplaceSuperposition_le_ray {Φ : ℝ → Y} {Ψ : ℝ → ℝ → Y} {ρ K : ℝ}
    (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hmeas : Measurable (Function.uncurry fun x s => ‖Ψ x s‖ₑ))
    (hΦ : ∀ x, ‖Φ x‖ₑ ≤ ∫⁻ s in Ioi (0 : ℝ), ‖Ψ x s‖ₑ)
    (hslice : ∀ s : ℝ, 0 < s → (∫⁻ x, ‖Ψ x s‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (K * Real.exp (-ρ * s))) :
    (∫⁻ x, ‖Φ x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (K / ρ) := by
  have hae : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      (∫⁻ x, ‖Ψ x s‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal (K * Real.exp (-ρ * s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hslice s hs
  have hbase := lintegral_sq_superposition_le_ae (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
    (Φ := Φ) (Ψ := Ψ) (w := fun s => ENNReal.ofReal (K * Real.exp (-ρ * s)))
    hmeas hΦ hae
  rwa [lintegral_exp_decay_Ioi hK hρ] at hbase

/-- An affine factor is dominated by a half-rate exponential. -/
theorem linear_le_exp_half {ρ s : ℝ} (hρ : 0 < ρ) (_hs : 0 ≤ s) :
    s ≤ (2 / ρ) * Real.exp (ρ / 2 * s) := by
  have h := Real.add_one_le_exp (ρ / 2 * s)
  have h2 : ρ / 2 * s ≤ Real.exp (ρ / 2 * s) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 / ρ)
  have h4 : (2 / ρ) * (ρ / 2 * s) = s := by field_simp
  rwa [h4] at h3

/-- The affine Laplace amplitude is dominated by two exponentials. -/
theorem linear_exp_le {K₀ K₁ ρ s : ℝ} (hK₁ : 0 ≤ K₁) (hρ : 0 < ρ) (hs : 0 ≤ s) :
    (K₀ + K₁ * s) * Real.exp (-ρ * s)
      ≤ K₀ * Real.exp (-ρ * s) + K₁ * (2 / ρ) * Real.exp (-(ρ / 2) * s) := by
  have hlin := linear_le_exp_half hρ hs
  have hexp : (0 : ℝ) < Real.exp (-ρ * s) := Real.exp_pos _
  have hsplit : Real.exp (ρ / 2 * s) * Real.exp (-ρ * s) = Real.exp (-(ρ / 2) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 := mul_le_mul_of_nonneg_left hlin hK₁
  have h2 := mul_le_mul_of_nonneg_right h1 hexp.le
  have hstep : K₁ * s * Real.exp (-ρ * s) ≤ K₁ * (2 / ρ) * Real.exp (-(ρ / 2) * s) := by
    calc K₁ * s * Real.exp (-ρ * s)
        ≤ K₁ * ((2 / ρ) * Real.exp (ρ / 2 * s)) * Real.exp (-ρ * s) := h2
      _ = K₁ * (2 / ρ) * (Real.exp (ρ / 2 * s) * Real.exp (-ρ * s)) := by ring
      _ = K₁ * (2 / ρ) * Real.exp (-(ρ / 2) * s) := by rw [hsplit]
  nlinarith [hstep]

/-- **The Laplace mass of a linearly growing amplitude.**  The extra power of the Laplace variable
costs one more power of the decay rate. -/
theorem lintegral_linear_exp_decay_Ioi_le {K₀ K₁ ρ : ℝ} (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁)
    (hρ : 0 < ρ) :
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((K₀ + K₁ * s) * Real.exp (-ρ * s)))
      ≤ ENNReal.ofReal (K₀ / ρ + 4 * K₁ / ρ ^ 2) := by
  have hρ2 : (0 : ℝ) < ρ / 2 := by linarith
  have hpt : ∀ s ∈ Ioi (0 : ℝ), ENNReal.ofReal ((K₀ + K₁ * s) * Real.exp (-ρ * s))
      ≤ ENNReal.ofReal (K₀ * Real.exp (-ρ * s))
        + ENNReal.ofReal (K₁ * (2 / ρ) * Real.exp (-(ρ / 2) * s)) := by
    intro s hs
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (linear_exp_le hK₁ hρ (le_of_lt hs))
  have hmeas₁ : Measurable fun s : ℝ => ENNReal.ofReal (K₀ * Real.exp (-ρ * s)) := by
    fun_prop
  calc (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal ((K₀ + K₁ * s) * Real.exp (-ρ * s)))
      ≤ ∫⁻ s in Ioi (0 : ℝ), (ENNReal.ofReal (K₀ * Real.exp (-ρ * s))
          + ENNReal.ofReal (K₁ * (2 / ρ) * Real.exp (-(ρ / 2) * s))) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (K₀ * Real.exp (-ρ * s)))
          + ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (K₁ * (2 / ρ) * Real.exp (-(ρ / 2) * s)) :=
        lintegral_add_left' hmeas₁.aemeasurable _
    _ = ENNReal.ofReal (K₀ / ρ) + ENNReal.ofReal (K₁ * (2 / ρ) / (ρ / 2)) := by
        rw [lintegral_exp_decay_Ioi hK₀ hρ,
          lintegral_exp_decay_Ioi (by positivity : (0 : ℝ) ≤ K₁ * (2 / ρ)) hρ2]
    _ = ENNReal.ofReal (K₀ / ρ + 4 * K₁ / ρ ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-- **The Laplace superposition bound with a linearly growing slice amplitude.**  The extra power of
the Laplace variable costs one more power of the decay rate — which is exactly what multiplication by
the frequency costs on a block slice. -/
theorem lintegral_sq_laplaceSuperposition_le_ray_linear {Φ : ℝ → Y} {Ψ : ℝ → ℝ → Y}
    {ρ K₀ K₁ : ℝ} (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hρ : 0 < ρ)
    (hmeas : Measurable (Function.uncurry fun x s => ‖Ψ x s‖ₑ))
    (hΦ : ∀ x, ‖Φ x‖ₑ ≤ ∫⁻ s in Ioi (0 : ℝ), ‖Ψ x s‖ₑ)
    (hslice : ∀ s : ℝ, 0 < s → (∫⁻ x, ‖Ψ x s‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal ((K₀ + K₁ * s) * Real.exp (-ρ * s))) :
    (∫⁻ x, ‖Φ x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (K₀ / ρ + 4 * K₁ / ρ ^ 2) := by
  have hae : ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))),
      (∫⁻ x, ‖Ψ x s‖ₑ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal ((K₀ + K₁ * s) * Real.exp (-ρ * s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hslice s hs
  have hbase := lintegral_sq_superposition_le_ae (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ).restrict (Ioi (0 : ℝ)))
    (Φ := Φ) (Ψ := Ψ) (w := fun s => ENNReal.ofReal ((K₀ + K₁ * s) * Real.exp (-ρ * s)))
    hmeas hΦ hae
  exact hbase.trans (lintegral_linear_exp_decay_Ioi_le hK₀ hK₁ hρ)

end GaloisForLFunctions.HTGeometry
