import GaloisForLFunctions.RHTower.DeningerPoissonBoundary

/-!
# The Poisson energy of a finite boundary datum

Scaling a mode by a coefficient scales its Dirichlet energy by the squared modulus, so a boundary
datum supported on finitely many characters has Poisson energy the weighted sum of the squared
coefficients, weighted by the absolute frequencies.

This is the energy identity on the trigonometric core, which is the boundary norm of the datum: the
Poisson extension is the minimal-energy filling and its energy is exactly that norm.

* `deningerModeProfile_sq_integrable` : the squared profile is integrable.
* `deningerPoisson_energy_coeff` : the energy of a scaled mode.
* `deningerPoisson_energy_finset` : the energy of a finite boundary datum.
-/

namespace RHTower

open MeasureTheory Set

section TraceEnergy

/-- **The squared Poisson profile is integrable on the half line.** -/
theorem deningerModeProfile_sq_integrable {μ : ℝ} (hμ : μ ≠ 0) :
    IntegrableOn (fun r => deningerModeProfile μ r ^ 2) (Ioi (0 : ℝ)) := by
  have hpos : (0 : ℝ) < 2 * |μ| := by
    have : 0 < |μ| := abs_pos.mpr hμ
    linarith
  have hsq : ∀ r : ℝ, deningerModeProfile μ r ^ 2 = Real.exp (-((2 * |μ|) * r)) := by
    intro r
    rw [deningerModeProfile, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [show (fun r : ℝ => deningerModeProfile μ r ^ 2)
      = fun r : ℝ => (fun x : ℝ => Real.exp (-x)) ((2 * |μ|) * r) from funext hsq]
  refine (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => Real.exp (-x)) 0 hpos).mpr ?_
  rw [mul_zero]
  exact integrableOn_exp_neg_Ioi 0

/-- The Dirichlet energy density of a scaled mode is integrable. -/
theorem deningerPoisson_energyDensity_integrable {μ : ℝ} (hμ : μ ≠ 0) (c : ℝ) :
    IntegrableOn (fun r => c * ((-|μ| * deningerModeProfile μ r) ^ 2
      + μ ^ 2 * deningerModeProfile μ r ^ 2)) (Ioi (0 : ℝ)) := by
  have hdens : ∀ r : ℝ, c * ((-|μ| * deningerModeProfile μ r) ^ 2
      + μ ^ 2 * deningerModeProfile μ r ^ 2)
      = (c * (2 * μ ^ 2)) * deningerModeProfile μ r ^ 2 := by
    intro r
    rw [deningerPoisson_energyDensity]
    ring
  rw [show (fun r : ℝ => c * ((-|μ| * deningerModeProfile μ r) ^ 2
      + μ ^ 2 * deningerModeProfile μ r ^ 2))
      = fun r : ℝ => (c * (2 * μ ^ 2)) * deningerModeProfile μ r ^ 2 from funext hdens]
  exact (deningerModeProfile_sq_integrable hμ).const_mul _

/-- **The Dirichlet energy of a scaled mode** is the squared coefficient times the absolute
frequency. -/
theorem deningerPoisson_energy_coeff {μ : ℝ} (hμ : μ ≠ 0) (c : ℝ) :
    (∫ r in Ioi (0 : ℝ), c * ((-|μ| * deningerModeProfile μ r) ^ 2
        + μ ^ 2 * deningerModeProfile μ r ^ 2)) = c * |μ| := by
  rw [integral_const_mul, deningerPoisson_energy hμ]

/-- **The Poisson energy of a finite boundary datum** is the sum of the squared coefficients
weighted by the absolute frequencies.  This is the boundary norm of the datum. -/
theorem deningerPoisson_energy_finset {ι : Type*} (S : Finset ι) (ℓ : ι → ℝ)
    (hℓ : ∀ a ∈ S, ℓ a ≠ 0) (φ : ι → ℂ) :
    (∫ r in Ioi (0 : ℝ), ∑ a ∈ S, ‖φ a‖ ^ 2 *
        ((-|ℓ a| * deningerModeProfile (ℓ a) r) ^ 2
          + (ℓ a) ^ 2 * deningerModeProfile (ℓ a) r ^ 2))
      = ∑ a ∈ S, ‖φ a‖ ^ 2 * |ℓ a| := by
  rw [MeasureTheory.integral_finsetSum S
    (fun a ha => deningerPoisson_energyDensity_integrable (hℓ a ha) (‖φ a‖ ^ 2))]
  exact Finset.sum_congr rfl fun a ha => deningerPoisson_energy_coeff (hℓ a ha) (‖φ a‖ ^ 2)

end TraceEnergy

end RHTower
