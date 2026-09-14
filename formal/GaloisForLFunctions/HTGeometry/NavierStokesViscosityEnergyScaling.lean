import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Navier-Stokes viscosity scaling of global energy

This file formalizes equation (10.23) from the supplied Navier-Stokes paper.  It separates
the argument into Haar-measure dilation, amplitude scaling, and the three-dimensional
specialization.  The final exponent is

`(√ν)⁵ = ν ^ (5 / 2)`:

* two powers come from squaring velocity amplitude `√ν`;
* three powers come from spatial volume under `x ↦ √ν x`.

For the dissipation term, the scaled gradient has no amplitude factor, while multiplication
by viscosity contributes the missing two powers.  The space-time theorem allows any time
measure, including Lebesgue measure restricted to the paper's interval `[0, 1]`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace GaloisForLFunctions.HTGeometry.NavierStokesViscosityEnergyScaling

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F]

/-- Squared norms acquire the spatial Jacobian under inverse scalar dilation.  This is the
measure-theoretic core of equation (10.23), stated for every finite-dimensional real space and
every additive Haar measure. -/
theorem integral_norm_sq_comp_inv_smul (μ : Measure E) [μ.IsAddHaarMeasure]
    (u : E → F) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, ‖u (R⁻¹ • x)‖ ^ 2 ∂μ) =
      R ^ Module.finrank ℝ E * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  simpa only [smul_eq_mul] using
    Measure.integral_comp_inv_smul_of_nonneg μ
      (fun x => ‖u x‖ ^ 2) hR

variable [NormedSpace ℝ F]

/-- Adding an amplitude factor `R` contributes two more powers to the spatial `L²` energy. -/
theorem integral_norm_sq_smul_comp_inv (μ : Measure E) [μ.IsAddHaarMeasure]
    (u : E → F) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x, ‖R • u (R⁻¹ • x)‖ ^ 2 ∂μ) =
      R ^ (Module.finrank ℝ E + 2) * ∫ x, ‖u x‖ ^ 2 ∂μ := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR, mul_pow]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_norm_sq_comp_inv_smul μ u hR]
  ring

/-- Spatial/amplitude viscosity rescaling of a field, as in equation (10.22). -/
def viscosityScaledField (ν : ℝ) (u : (Fin 3 → ℝ) → F) (x : Fin 3 → ℝ) : F :=
  Real.sqrt ν • u ((Real.sqrt ν)⁻¹ • x)

/-- In dimension three, the five powers of `√ν` are exactly the paper's `ν^(5/2)`. -/
theorem sqrt_pow_five_eq_rpow_five_halves (ν : ℝ≥0) :
    Real.sqrt (ν : ℝ) ^ 5 = (ν : ℝ) ^ (5 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul ν.coe_nonneg]
  norm_num

/-- **Equation (10.23), kinetic-energy form.** Three-dimensional spatial `L²` energy
acquires five powers of `√ν`. -/
theorem kineticEnergy_viscosityScaledField_sqrt (ν : ℝ)
    (u : (Fin 3 → ℝ) → F) :
    (∫ x, ‖viscosityScaledField ν u x‖ ^ 2 ∂volume) =
      Real.sqrt ν ^ 5 * ∫ x, ‖u x‖ ^ 2 ∂volume := by
  simpa [viscosityScaledField] using
    integral_norm_sq_smul_comp_inv (volume : Measure (Fin 3 → ℝ)) u
      (R := Real.sqrt ν) (Real.sqrt_nonneg ν)

/-- Equation (10.23) with the paper's literal exponent `ν^(5/2)`. -/
theorem kineticEnergy_viscosityScaledField (ν : ℝ≥0)
    (u : (Fin 3 → ℝ) → F) :
    (∫ x, ‖viscosityScaledField ν u x‖ ^ 2 ∂volume) =
      (ν : ℝ) ^ (5 / 2 : ℝ) * ∫ x, ‖u x‖ ^ 2 ∂volume := by
  rw [← sqrt_pow_five_eq_rpow_five_halves]
  exact kineticEnergy_viscosityScaledField_sqrt ν u

omit [NormedSpace ℝ F] in
/-- **Equation (10.23), spatial dissipation form.** A gradient-like field composed with
`x ↦ x / √ν`, then weighted by viscosity, has the same `ν^(5/2)` scaling. -/
theorem viscosityWeightedDissipation_viscosityScaledField (ν : ℝ≥0)
    (g : (Fin 3 → ℝ) → F) :
    (ν : ℝ) * (∫ x, ‖g ((Real.sqrt ν)⁻¹ • x)‖ ^ 2 ∂volume) =
      (ν : ℝ) ^ (5 / 2 : ℝ) * ∫ x, ‖g x‖ ^ 2 ∂volume := by
  rw [← sqrt_pow_five_eq_rpow_five_halves]
  rw [integral_norm_sq_comp_inv_smul (volume : Measure (Fin 3 → ℝ)) g
    (R := Real.sqrt ν) (Real.sqrt_nonneg ν)]
  have hfin : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  rw [hfin]
  nth_rewrite 1 [← Real.sq_sqrt ν.coe_nonneg]
  ring

variable {T : Type*} [MeasurableSpace T]

omit [NormedSpace ℝ F] in
/-- **Equation (10.23), space-time dissipation form.** The spatial identity survives
integration against any time measure.  Taking `τ = volume.restrict (Set.Icc 0 1)` gives the
paper's integral from time zero to one. -/
theorem viscosityWeightedSpaceTimeDissipation_viscosityScaledField (ν : ℝ≥0)
    (τ : Measure T) (g : T → (Fin 3 → ℝ) → F) :
    (ν : ℝ) * (∫ t, ∫ x, ‖g t ((Real.sqrt ν)⁻¹ • x)‖ ^ 2 ∂volume ∂τ) =
      (ν : ℝ) ^ (5 / 2 : ℝ) *
        ∫ t, ∫ x, ‖g t x‖ ^ 2 ∂volume ∂τ := by
  rw [← sqrt_pow_five_eq_rpow_five_halves]
  have hfin : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by simp
  simp_rw [integral_norm_sq_comp_inv_smul (volume : Measure (Fin 3 → ℝ))
    (g _) (R := Real.sqrt ν) (Real.sqrt_nonneg ν), hfin]
  rw [MeasureTheory.integral_const_mul]
  nth_rewrite 1 [← Real.sq_sqrt ν.coe_nonneg]
  ring

end GaloisForLFunctions.HTGeometry.NavierStokesViscosityEnergyScaling
