import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import GaloisForLFunctions.HTGeometry.L2FourierIntegralBridge
import GaloisForLFunctions.HTGeometry.L2PairingEnergy

/-!
# The half-line Laplace transform on a vertical line is a Fourier transform

Restricted to the line `Re w = σ`, the half-line Laplace transform of `φ` is the Fourier transform
of the damped datum `1_{x>0}φ(x)e^{-σx}`.  Plancherel then gives the exact mass of the transform on
that line, which is the isometry half of the Paley--Wiener description of the Hardy space of a
half-plane.

## Main results

* `fourierIntegral_rayDamp`
* `integral_norm_sq_laplaceRay_line`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology FourierTransform

noncomputable section

/-- The point of the vertical line `Re w = σ` at Fourier frequency `ξ`. -/
def rayLine (σ ξ : ℝ) : ℂ := (σ : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I

@[simp] theorem rayLine_re (σ ξ : ℝ) : (rayLine σ ξ).re = σ := by
  simp [rayLine]

/-- The datum damped by `e^{-σx}` and extended by zero to the left half-line. -/
def rayDamp (φ : ℝ → ℂ) (σ : ℝ) : ℝ → ℂ :=
  Set.indicator (Ioi (0 : ℝ)) fun x => φ x * expRay ((σ : ℝ) : ℂ) x

theorem memLp_two_rayDamp {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℝ} (hσ : 0 ≤ σ) : MemLp (rayDamp φ σ) 2 volume := by
  rw [rayDamp, memLp_indicator_iff_restrict measurableSet_Ioi]
  refine MemLp.mono hφ ?_ ?_
  · exact hφ.aestronglyMeasurable.mul (continuous_expRay _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_expRay]
    have hre : ((σ : ℝ) : ℂ).re = σ := Complex.ofReal_re σ
    rw [hre]
    have hle : Real.exp (-(σ * x)) ≤ 1 := by
      refine Real.exp_le_one_iff.2 ?_
      have : 0 ≤ σ * x := mul_nonneg hσ (le_of_lt hx)
      linarith
    nlinarith [norm_nonneg (φ x), Real.exp_pos (-(σ * x))]

theorem integrable_rayDamp {φ : ℝ → ℂ} (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))))
    {σ : ℝ} (hσ : 0 < σ) : Integrable (rayDamp φ σ) volume := by
  have hre : (0 : ℝ) < ((σ : ℝ) : ℂ).re := by rwa [Complex.ofReal_re]
  rw [rayDamp, integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_laplaceRay hφ hre

/-- **On a vertical line the Laplace transform is the Fourier transform of the damped datum.** -/
theorem fourierIntegral_rayDamp (φ : ℝ → ℂ) (σ ξ : ℝ) :
    𝓕 (rayDamp φ σ) ξ = laplaceRay φ (rayLine σ ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, laplaceRay, rayDamp,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Set.indicator_apply, smul_eq_mul]
  by_cases hv : v ∈ Ioi (0 : ℝ)
  · rw [if_pos hv, if_pos hv, expRay, expRay]
    have hsum : ((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I + -(((σ : ℝ) : ℂ) * (v : ℝ))
        = -(rayLine σ ξ * (v : ℝ)) := by
      rw [rayLine]
      push_cast
      ring
    calc Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)
            * (φ v * Complex.exp (-(((σ : ℝ) : ℂ) * (v : ℝ))))
        = φ v * (Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I)
            * Complex.exp (-(((σ : ℝ) : ℂ) * (v : ℝ)))) := by ring
      _ = φ v * Complex.exp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * Complex.I
            + -(((σ : ℝ) : ℂ) * (v : ℝ))) := by rw [← Complex.exp_add]
      _ = φ v * Complex.exp (-(rayLine σ ξ * (v : ℝ))) := by rw [hsum]
  · rw [if_neg hv, if_neg hv, mul_zero]

/-- The `L²` Fourier transform of the damped datum is the Laplace transform on the line. -/
theorem coeFn_fourierTransform_rayDamp {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ) :
    ((𝓕 ((memLp_two_rayDamp hφ hσ.le).toLp (rayDamp φ σ)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] fun ξ : ℝ => laplaceRay φ (rayLine σ ξ) := by
  have hgm : MemLp (rayDamp φ σ) 2 volume := memLp_two_rayDamp hφ hσ.le
  have hgi : Integrable (rayDamp φ σ) volume := integrable_rayDamp hφ hσ
  have hGcoe : ((hgm.toLp (rayDamp φ σ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume] rayDamp φ σ := hgm.coeFn_toLp
  have hGint : Integrable ((hgm.toLp (rayDamp φ σ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      volume := hgi.congr hGcoe.symm
  have hbridge := coeFn_fourierTransform_ae_eq_fourierIntegral
    (hgm.toLp (rayDamp φ σ)) hGint
  filter_upwards [hbridge] with ξ hξ
  rw [hξ, Real.Lp.fourierTransform_apply]
  have hcoe : (((memLp_one_iff_integrable.mpr hGint).toLp
      ((hgm.toLp (rayDamp φ σ) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) : ℝ → ℂ)
      =ᵐ[volume] rayDamp φ σ :=
    ((memLp_one_iff_integrable.mpr hGint).coeFn_toLp).trans hGcoe
  have hcg := Real.fourier_congr_ae hcoe ξ
  rw [hcg, fourierIntegral_rayDamp]

/-- The Laplace transform is square-integrable on every vertical line of the half-plane. -/
theorem memLp_two_laplaceRay_line {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ) :
    MemLp (fun ξ : ℝ => laplaceRay φ (rayLine σ ξ)) 2 volume :=
  (Lp.memLp _).ae_eq (coeFn_fourierTransform_rayDamp hφ hσ)

/-- **Plancherel on a vertical line.** -/
theorem integral_norm_sq_laplaceRay_line {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) {σ : ℝ} (hσ : 0 < σ) :
    (∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ (2 : ℕ))
      = ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ (2 : ℕ) := by
  have hgm : MemLp (rayDamp φ σ) 2 volume := memLp_two_rayDamp hφ hσ.le
  set G : Lp ℂ 2 (volume : Measure ℝ) := hgm.toLp (rayDamp φ σ) with hG
  have hGcoe : (G : ℝ → ℂ) =ᵐ[volume] rayDamp φ σ := hgm.coeFn_toLp
  have hfour := coeFn_fourierTransform_rayDamp hφ hσ
  have hlhs : (∫ ξ : ℝ, ‖laplaceRay φ (rayLine σ ξ)‖ ^ (2 : ℕ))
      = ‖(𝓕 G : Lp ℂ 2 (volume : Measure ℝ))‖ ^ (2 : ℕ) := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    refine (integral_congr_ae ?_).symm
    filter_upwards [hfour] with ξ hξ
    rw [hξ]
  have hrhs : ‖G‖ ^ (2 : ℕ) = ∫ x in Ioi (0 : ℝ), Real.exp (-(2 * σ * x)) * ‖φ x‖ ^ (2 : ℕ) := by
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hstep : (∫ x : ℝ, ‖(G : ℝ → ℂ) x‖ ^ (2 : ℕ)) = ∫ x : ℝ, ‖rayDamp φ σ x‖ ^ (2 : ℕ) := by
      refine integral_congr_ae ?_
      filter_upwards [hGcoe] with x hx
      rw [hx]
    rw [hstep, rayDamp, ← MeasureTheory.integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Set.indicator_apply]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [if_pos hx, if_pos hx, norm_mul, mul_pow, norm_sq_expRay, Complex.ofReal_re]
      ring
    · rw [if_neg hx, if_neg hx, norm_zero]
      ring
  rw [hlhs, Lp.norm_fourier_eq, hrhs]

end

end GaloisForLFunctions.HTGeometry
