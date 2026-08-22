import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier

/-!
# The Hardy space of the right half-plane

A function is in the Hardy space `H²` of the right half-plane when it is holomorphic there and its
restrictions to the vertical lines `Re w = σ` have uniformly bounded `L²` mass.  The half-line
Laplace transform of an `L²(0,∞)` datum belongs to that class, with the mass of the datum as bound,
and the masses on the lines increase to the mass of the datum as the line approaches the boundary.
This is the easy direction of the Paley--Wiener description of `H²`.

## Main results

* `IsHalfPlaneHardy`
* `isHalfPlaneHardy_laplaceRay`
* `tendsto_integral_norm_sq_laplaceRay_line`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

noncomputable section

/-- The Hardy space of the right half-plane: holomorphic on `Re w > 0` with the `L²` mass on every
vertical line bounded by `M`. -/
structure IsHalfPlaneHardy (F : ℂ → ℂ) (M : ℝ) : Prop where
  /-- Holomorphy on the open right half-plane. -/
  holo : DifferentiableOn ℂ F {w : ℂ | 0 < w.re}
  /-- Square-integrability on every vertical line inside the half-plane. -/
  memLp : ∀ σ : ℝ, 0 < σ → MemLp (fun ξ : ℝ => F (rayLine σ ξ)) 2 volume
  /-- A uniform bound for the mass on the lines. -/
  bound : ∀ σ : ℝ, 0 < σ → (∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2) ≤ M

theorem integrableOn_exp_mul_norm_sq {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ 2) (Ioi (0 : ℝ)) := by
  refine (integrableOn_norm_sq_of_memLp hφ).mono' ?_ ?_
  · exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      ((hφ.aestronglyMeasurable.norm).pow 2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hle : Real.exp (-(2 * σ * x)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      nlinarith
    have hpos : (0 : ℝ) < Real.exp (-(2 * σ * x)) := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg ‖φ x‖]

/-- **Paley--Wiener, easy direction.**  The half-line Laplace transform of an `L²` datum lies in the
Hardy space of the right half-plane, with the mass of the datum as bound. -/
theorem isHalfPlaneHardy_laplaceRay {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    IsHalfPlaneHardy (laplaceRay φ) (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2) where
  holo := differentiableOn_laplaceRay hφ
  memLp := fun σ hσ => memLp_two_laplaceRay_line hφ hσ
  bound := fun σ hσ => by
    rw [integral_norm_sq_laplaceRay_line hφ hσ]
    refine setIntegral_mono_on (integrableOn_exp_mul_norm_sq hφ hσ)
      (integrableOn_norm_sq_of_memLp hφ) measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have hle : Real.exp (-(2 * σ * x)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      nlinarith
    nlinarith [sq_nonneg ‖φ x‖, Real.exp_pos (-(2 * σ * x))]

/-- The mass on the vertical lines increases to the mass of the datum as the line approaches the
boundary of the half-plane. -/
theorem tendsto_integral_norm_sq_laplaceRay_line {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Tendsto (fun σ : ℝ => ∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x in Ioi (0 : ℝ), ‖φ x‖ ^ 2)) := by
  have hev : (fun σ : ℝ => ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] fun σ : ℝ => ∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (integral_norm_sq_laplaceRay_line hφ hσ).symm
  refine Tendsto.congr' hev ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => ‖φ x‖ ^ 2) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (Real.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      ((hφ.aestronglyMeasurable.norm).pow 2)
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hσ0 : (0 : ℝ) < σ := hσ
    have hle : Real.exp (-(2 * σ * x)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg ‖φ x‖, Real.exp_pos (-(2 * σ * x))]
  · exact integrableOn_norm_sq_of_memLp hφ
  · filter_upwards with x
    have hcontf : Continuous (fun σ : ℝ => Real.exp (-(2 * σ * x))) := by fun_prop
    have hcont : Tendsto (fun σ : ℝ => Real.exp (-(2 * σ * x))) (𝓝[>] (0 : ℝ))
        (𝓝 (Real.exp (-(2 * (0 : ℝ) * x)))) :=
      (hcontf.tendsto 0).mono_left nhdsWithin_le_nhds
    have h0 : Real.exp (-(2 * (0 : ℝ) * x)) = 1 := by norm_num
    rw [h0] at hcont
    simpa using hcont.mul_const (‖φ x‖ ^ 2)

end

end GaloisForLFunctions.HTGeometry
