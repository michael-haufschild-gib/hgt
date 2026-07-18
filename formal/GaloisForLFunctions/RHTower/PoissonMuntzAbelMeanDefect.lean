import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.RHTower.PoissonAbelBoundary

/-!
# The Poisson--Muntz Abel mean-defect law

For an even real `L1` source, the one-sided Abel sum of its positive Fourier samples is
controlled by the boundary value of the scaled periodization.  There is exactly one correction:
the zero-frequency mean.  In particular, a zero-mean source cancels the whole defect.

The theorem is stated at a symmetric Lebesgue point, so no continuity or endpoint convention is
hidden in the periodization.
-/

open Real MeasureTheory Set intervalIntegral Filter Topology Function
open scoped ENNReal FourierTransform

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The real periodization at aperture `a`: first dilate the source, then sum its integer
translates. -/
def poissonMuntzScaledPeriodization (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  realL1Periodization (fun y => f (y / a)) x

/-- The angular form of the scaled periodization on `[-π, π]`. -/
def poissonMuntzAngularDatum (f : ℝ → ℝ) (a t : ℝ) : ℝ :=
  poissonMuntzScaledPeriodization f a (t / (2 * Real.pi))

/-- The positive-frequency Abel tail, indexed so that the first term is the sample at `a`. -/
def poissonMuntzAbelSum (f : ℝ → ℝ) (a r : ℝ) : ℂ :=
  ∑' n : ℕ, (r : ℂ) ^ (n + 1) *
    𝓕 (fun x => (f x : ℂ)) (a * (n + 1 : ℝ))

/-- The angular datum is interval-integrable for every positive aperture. -/
theorem intervalIntegrable_poissonMuntzAngularDatum
    {f : ℝ → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable (poissonMuntzAngularDatum f a) volume (-Real.pi) Real.pi := by
  have hscaled : Integrable (fun y : ℝ => f (y / a)) := hf.comp_div ha.ne'
  have hcell : IntervalIntegrable
      (realL1Periodization (fun y => f (y / a))) volume
      (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
    convert intervalIntegrable_realL1Periodization_unitCell
      hscaled (-(1 / 2 : ℝ)) using 1
    norm_num
  have hcomp := hcell.comp_mul_left (c := (2 * Real.pi)⁻¹)
  convert hcomp using 1
  · funext t
    simp only [poissonMuntzAngularDatum, poissonMuntzScaledPeriodization, div_eq_mul_inv]
    rw [mul_comm]
  · field_simp [Real.pi_ne_zero]
  · field_simp [Real.pi_ne_zero]

/-- On the angular scale, the integer Fourier character is the ordinary phase
`exp(i t) ^ m`. -/
theorem fourier_apply_div_two_pi (m : ℤ) (t : ℝ) :
    fourier m ((t / (2 * Real.pi) : ℝ) : UnitAddCircle) =
      Complex.exp (t * Complex.I) ^ m := by
  rw [fourier_coe_apply, ← Complex.exp_int_mul]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The normalized angular coefficient of the scaled periodization is the Euclidean Fourier
sample at the oppositely signed lattice frequency. -/
theorem normalized_integral_poissonMuntzAngularDatum_mul_phase_eq
    {f : ℝ → ℝ} (hf : Integrable f) {a : ℝ} (ha : 0 < a) (m : ℤ) :
    (2 * Real.pi : ℂ)⁻¹ *
        ∫ t in (-Real.pi)..Real.pi,
          Complex.exp (t * Complex.I) ^ m * (poissonMuntzAngularDatum f a t : ℂ) =
      a • 𝓕 (fun x => (f x : ℂ)) (a * (-(m : ℝ))) := by
  let F : ℝ → ℂ := fun x =>
    fourier m (x : UnitAddCircle) *
      (realL1Periodization (fun y => f (y / a)) x : ℂ)
  have hchange := intervalIntegral.integral_comp_div
    (a := -Real.pi) (b := Real.pi) F
    (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  have hfun : (fun t : ℝ =>
      Complex.exp (t * Complex.I) ^ m * (poissonMuntzAngularDatum f a t : ℂ)) =
      fun t : ℝ => F (t / (2 * Real.pi)) := by
    funext t
    simp only [F, poissonMuntzAngularDatum, poissonMuntzScaledPeriodization]
    rw [fourier_apply_div_two_pi]
  rw [hfun, hchange]
  have hcoeff := integral_centered_scaled_realL1Periodization_mul_fourier_eq
    hf ha (-m)
  have hcoeff' :
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), F x =
        a • 𝓕 (fun x => (f x : ℂ)) (a * (-(m : ℝ))) := by
    simpa only [F, neg_neg, Int.cast_neg] using hcoeff
  rw [show -Real.pi / (2 * Real.pi) = -(1 / 2 : ℝ) by
        field_simp [Real.pi_ne_zero] <;> ring,
      show Real.pi / (2 * Real.pi) = (1 / 2 : ℝ) by
        field_simp [Real.pi_ne_zero] <;> ring,
      hcoeff']
  simp only [Complex.real_smul]
  field_simp [Real.pi_ne_zero]
  ring

/-- Reflection invariance of a real source passes exactly to its Euclidean Fourier transform. -/
theorem even_fourier_ofReal {f : ℝ → ℝ} (hf : Function.Even f) :
    Function.Even (𝓕 (fun x => (f x : ℂ))) := by
  let g : ℝ → ℂ := fun x => (f x : ℂ)
  have hg : g ∘ (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) = g := by
    funext x
    change (f (-x) : ℂ) = (f x : ℂ)
    exact congrArg (fun y : ℝ => (y : ℂ)) (hf x)
  intro w
  have hreflect := Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) g w
  rw [hg] at hreflect
  exact hreflect.symm

end RHTower
