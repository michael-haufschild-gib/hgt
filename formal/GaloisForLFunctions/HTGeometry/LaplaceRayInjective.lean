import GaloisForLFunctions.HTGeometry.HalfLineLaplaceFourier

noncomputable section

/-!
# Injectivity of the half-line Laplace transform

A square-integrable datum on the positive ray whose Laplace transform vanishes on the whole open
right half-plane is zero.

Only one vertical line is needed: on the line `Re w = 1` the Laplace transform is the Fourier
transform of the datum damped by `e^{-x}`, so vanishing there makes the damped datum zero by
injectivity of the `L²` Fourier transform, and the damping factor never vanishes.
-/

open MeasureTheory Set Complex Filter Topology FourierTransform

namespace GaloisForLFunctions.HTGeometry

/-- **Injectivity of the half-line Laplace transform, with one point removed.**  Vanishing on the
open right half-plane away from a single point already forces the datum to vanish: the exceptional
point meets the test line `Re w = 1` in a null set of parameters. -/
theorem ae_eq_zero_of_laplaceRay_eq_zero_of_ne {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ)))) (w₀ : ℂ)
    (h0 : ∀ w : ℂ, 0 < w.re → w ≠ w₀ → laplaceRay φ w = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), φ x = 0 := by
  have hσ : (0 : ℝ) < 1 := one_pos
  have hpi := Real.pi_pos
  have hnull : volume ({w₀.im / (2 * Real.pi)} : Set ℝ) = 0 := by simp
  have hzero : ((𝓕 ((memLp_two_rayDamp hφ hσ.le).toLp (rayDamp φ 1)) :
      Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] fun _ => (0 : ℂ) := by
    refine (coeFn_fourierTransform_rayDamp hφ hσ).trans ?_
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with ξ hξ
    refine h0 (rayLine 1 ξ) (by simp) ?_
    intro hcon
    refine hξ ?_
    have him : (rayLine 1 ξ).im = w₀.im := by rw [hcon]
    have hlin : 2 * Real.pi * ξ = w₀.im := by simpa [rayLine] using him
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith
  have hLp : (𝓕 ((memLp_two_rayDamp hφ hσ.le).toLp (rayDamp φ 1)) :
      Lp ℂ 2 (volume : Measure ℝ)) = 0 := by
    refine MeasureTheory.Lp.ext (hzero.trans ?_)
    exact (MeasureTheory.Lp.coeFn_zero ℂ 2 volume).symm
  have hd : (memLp_two_rayDamp hφ hσ.le).toLp (rayDamp φ 1) = 0 := by
    refine (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).injective ?_
    show (𝓕 ((memLp_two_rayDamp hφ hσ.le).toLp (rayDamp φ 1)) : Lp ℂ 2 (volume : Measure ℝ))
      = (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) 0
    rw [hLp]
    exact (map_zero (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)).symm
  have hae : rayDamp φ 1 =ᵐ[volume] fun _ => (0 : ℂ) := by
    refine ((memLp_two_rayDamp hφ hσ.le).coeFn_toLp).symm.trans ?_
    rw [hd]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 volume
  have haer : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), rayDamp φ 1 x = 0 :=
    ae_restrict_of_ae hae
  filter_upwards [haer, ae_restrict_mem measurableSet_Ioi] with x hx hmem
  rw [rayDamp, Set.indicator_of_mem hmem] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact h
  · exact absurd h (Complex.exp_ne_zero _)

/-- **Injectivity of the half-line Laplace transform on `L²`.**  A square-integrable datum on the
positive ray whose Laplace transform vanishes on the open right half-plane is itself zero. -/
theorem ae_eq_zero_of_laplaceRay_eq_zero {φ : ℝ → ℂ}
    (hφ : MemLp φ 2 (volume.restrict (Ioi (0 : ℝ))))
    (h0 : ∀ w : ℂ, 0 < w.re → laplaceRay φ w = 0) :
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), φ x = 0 :=
  ae_eq_zero_of_laplaceRay_eq_zero_of_ne hφ 0 fun w hw _ => h0 w hw


end GaloisForLFunctions.HTGeometry
