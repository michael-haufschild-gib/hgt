import GaloisForLFunctions.RHTower.DeningerKummerGaussianProbe

/-!
# The endpoint-corrected Gaussian core

A finite combination of Gaussian probes has value at the origin the sum of its coefficients, and
Fourier transform at the origin — that is, total integral — the sum of the coefficients divided by
the widths.  So the two Meyer endpoint conditions, vanishing at the cone apex and vanishing
Fourier trace, are exactly the two Gaussian moment relations, and they are exactly the vanishing of
the associated exponential polynomial at `0` and at `1`.

* `deningerGaussianCombo` : the finite Gaussian combination `(5)`.
* `deningerGaussianCombo_zero`, `deningerGaussianCombo_integral` : the two moments `(6)`.
* `deningerEndpointCorrected_iff` : the endpoint conditions are the moment relations `(7)`.
* `deningerExpPoly_endpoints` : and they are the vanishing of `(11)` at `0` and `1`, i.e. `(12)`.
-/

namespace RHTower

open Complex MeasureTheory Set
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

section EndpointCore

variable {N : ℕ} {c : Fin N → ℂ} {μ : Fin N → ℝ}

/-- The Gaussian probe is integrable. -/
theorem deningerGaussianProbe_integrable {ν : ℝ} (hν : 0 < ν) :
    Integrable (deningerGaussianProbe ν) := by
  have hb : (0 : ℝ) < Real.pi * ν ^ 2 := by positivity
  have hreal : Integrable fun x : ℝ => Real.exp (-(Real.pi * ν ^ 2) * x ^ 2) :=
    integrable_exp_neg_mul_sq hb
  have hfun : deningerGaussianProbe ν
      = fun x : ℝ => ((Real.exp (-(Real.pi * ν ^ 2) * x ^ 2) : ℝ) : ℂ) := by
    funext x
    rw [deningerGaussianProbe_apply]
    congr 1
    ring_nf
  rw [hfun]
  exact hreal.ofReal

/-- **The total integral of a Gaussian probe** is the reciprocal of its width. -/
theorem deningerGaussianProbe_integral {ν : ℝ} (hν : 0 < ν) :
    (∫ x : ℝ, deningerGaussianProbe ν x) = ((ν : ℂ))⁻¹ := by
  have hfun : deningerGaussianProbe ν
      = fun x : ℝ => ((Real.exp (-(Real.pi * ν ^ 2) * x ^ 2) : ℝ) : ℂ) := by
    funext x
    rw [deningerGaussianProbe_apply]
    congr 1
    ring_nf
  rw [hfun, integral_complex_ofReal, integral_gaussian]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (Real.pi / (Real.pi * ν ^ 2)) = ν⁻¹ := by
    rw [show Real.pi / (Real.pi * ν ^ 2) = (ν⁻¹) ^ 2 by
      field_simp]
    exact Real.sqrt_sq (le_of_lt (inv_pos.mpr hν))
  rw [hsqrt]
  push_cast
  ring

/-- A finite Gaussian combination. -/
noncomputable def deningerGaussianCombo (c : Fin N → ℂ) (μ : Fin N → ℝ) (x : ℝ) : ℂ :=
  ∑ j, c j * deningerGaussianProbe (μ j) x

/-- **The value at the cone apex** is the sum of the coefficients. -/
theorem deningerGaussianCombo_zero (c : Fin N → ℂ) (μ : Fin N → ℝ) :
    deningerGaussianCombo c μ 0 = ∑ j, c j := by
  rw [deningerGaussianCombo]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deningerGaussianProbe_zero, mul_one]

/-- A finite Gaussian combination is integrable. -/
theorem deningerGaussianCombo_integrable (hμ : ∀ j, 0 < μ j) :
    Integrable (deningerGaussianCombo c μ) := by
  have hfun : deningerGaussianCombo c μ
      = fun x : ℝ => ∑ j, c j * deningerGaussianProbe (μ j) x := rfl
  rw [hfun]
  exact integrable_finsetSum _ fun j _ =>
    (deningerGaussianProbe_integrable (hμ j)).const_mul _

/-- **The Fourier trace** of a finite Gaussian combination is the sum of the coefficients divided
by the widths. -/
theorem deningerGaussianCombo_integral (hμ : ∀ j, 0 < μ j) :
    (∫ x : ℝ, deningerGaussianCombo c μ x) = ∑ j, c j / (μ j : ℂ) := by
  have hfun : deningerGaussianCombo c μ
      = fun x : ℝ => ∑ j, c j * deningerGaussianProbe (μ j) x := rfl
  rw [hfun]
  rw [integral_finsetSum _ fun j _ =>
    (deningerGaussianProbe_integrable (hμ j)).const_mul (c j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, deningerGaussianProbe_integral (hμ j), div_eq_mul_inv]

/-- The Fourier transform at the origin is the total integral. -/
theorem deningerFourier_zero (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  simp [Real.fourier_eq]

/-- The two Meyer endpoint conditions. -/
def deningerEndpointCorrected (c : Fin N → ℂ) (μ : Fin N → ℝ) : Prop :=
  (∑ j, c j) = 0 ∧ (∑ j, c j / (μ j : ℂ)) = 0

/-- **The endpoint conditions are the two Gaussian moment relations.** -/
theorem deningerEndpointCorrected_iff (hμ : ∀ j, 0 < μ j) :
    (deningerGaussianCombo c μ 0 = 0 ∧ 𝓕 (deningerGaussianCombo c μ) 0 = 0)
      ↔ deningerEndpointCorrected c μ := by
  rw [deningerGaussianCombo_zero, deningerFourier_zero,
    deningerGaussianCombo_integral hμ, deningerEndpointCorrected]

/-- The exponential polynomial of a Gaussian combination. -/
noncomputable def deningerExpPoly (c : Fin N → ℂ) (μ : Fin N → ℝ) (s : ℂ) : ℂ :=
  ∑ j, c j * (μ j : ℂ) ^ (-s)

theorem deningerExpPoly_zero (c : Fin N → ℂ) (μ : Fin N → ℝ) :
    deningerExpPoly c μ 0 = ∑ j, c j := by
  rw [deningerExpPoly]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [neg_zero, Complex.cpow_zero, mul_one]

theorem deningerExpPoly_one (c : Fin N → ℂ) (μ : Fin N → ℝ) :
    deningerExpPoly c μ 1 = ∑ j, c j / (μ j : ℂ) := by
  rw [deningerExpPoly]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.cpow_neg_one, div_eq_mul_inv]

/-- **The endpoint conditions are the vanishing of the exponential polynomial at `0` and `1`.** -/
theorem deningerExpPoly_endpoints (c : Fin N → ℂ) (μ : Fin N → ℝ) :
    (deningerExpPoly c μ 0 = 0 ∧ deningerExpPoly c μ 1 = 0)
      ↔ deningerEndpointCorrected c μ := by
  rw [deningerExpPoly_zero c μ, deningerExpPoly_one c μ, deningerEndpointCorrected]

end EndpointCore

end RHTower
