import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaScaling
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Tactic

/-!
# Closed sech-profile hydrodynamics from arXiv:2607.21750

The positive corpus `sech` profile supplies an everywhere-invertible curvature.  Consequently the
paper's density, torsion-induced velocity, mass current, momentum current, and Bohm term can all be
constructed without nonvanishing hypotheses.  Their continuity and stationary momentum equations
are certified with actual `HasDerivAt` witnesses.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def sechCurvatureUnit (x : ℝ) : ℝˣ :=
  Units.mk0 (solitonA x) (solitonA_pos x).ne'

@[simp] theorem coe_sechCurvatureUnit (x : ℝ) :
    (sechCurvatureUnit x : ℝ) = solitonA x := rfl

noncomputable def sechDensity (x : ℝ) : ℝ := density (sechCurvatureUnit x)

noncomputable def sechFluidSpeed (D x : ℝ) : ℝ :=
  fluidSpeed D 1 1 (sechCurvatureUnit x)

noncomputable def sechMassCurrent (D x : ℝ) : ℝ :=
  sechDensity x * sechFluidSpeed D x

noncomputable def sechMomentumCurrent (D x : ℝ) : ℝ :=
  sechDensity x * sechFluidSpeed D x ^ 2

noncomputable def sechQuantumStress (D x : ℝ) : ℝ :=
  4 * D ^ 2 / solitonA x ^ 2

noncomputable def sechMomentumDerivative (D x : ℝ) : ℝ :=
  -8 * D ^ 2 * solitonA1 x / solitonA x ^ 3

/-- The paper's hydrodynamic density is exactly the corpus `sech²` profile. -/
theorem sechDensity_eq (x : ℝ) : sechDensity x = solitonQ x := by
  rw [sechDensity, density, coe_sechCurvatureUnit, solitonA_sq]

/-- Equation (57), now as a closed law along the full `sech` curvature profile. -/
theorem sechMassCurrent_eq (D x : ℝ) : sechMassCurrent D x = 2 * D := by
  simpa [sechMassCurrent, sechDensity, sechFluidSpeed] using
    density_mul_fluidSpeed D 1 1 (sechCurvatureUnit x)

/-- Momentum current is pointwise identical to the paper's inverse-curvature stress. -/
theorem sechMomentumCurrent_eq (D x : ℝ) :
    sechMomentumCurrent D x = sechQuantumStress D x := by
  simpa [sechMomentumCurrent, sechDensity, sechFluidSpeed, sechQuantumStress] using
    density_mul_fluidSpeed_sq D 1 1 (sechCurvatureUnit x)

/-- The mass current has zero spatial divergence. -/
theorem hasDerivAt_sechMassCurrent (D x : ℝ) :
    HasDerivAt (sechMassCurrent D) 0 x := by
  have hfun : sechMassCurrent D = fun _ : ℝ => 2 * D := by
    funext y
    exact sechMassCurrent_eq D y
  rw [hfun]
  exact hasDerivAt_const x (2 * D)

/-- Exact derivative of the inverse-curvature quantum-stress term. -/
theorem hasDerivAt_sechQuantumStress (D x : ℝ) :
    HasDerivAt (sechQuantumStress D) (sechMomentumDerivative D x) x := by
  have hA0 : solitonA x ≠ 0 := (solitonA_pos x).ne'
  have hden : HasDerivAt (fun y : ℝ => solitonA y ^ 2)
      (2 * solitonA x * solitonA1 x) x := by
    have hp := (hasDerivAt_solitonA x).pow 2
    apply (hp.congr_deriv (by ring)).congr_of_eventuallyEq
    filter_upwards with y
    rfl
  have h := (hasDerivAt_const x (4 * D ^ 2)).div hden (pow_ne_zero 2 hA0)
  apply h.congr_deriv
  rw [sechMomentumDerivative]
  simp only [zero_mul, zero_sub]
  field_simp
  ring

/-- Momentum current has the same derivative because it is the quantum stress. -/
theorem hasDerivAt_sechMomentumCurrent (D x : ℝ) :
    HasDerivAt (sechMomentumCurrent D) (sechMomentumDerivative D x) x := by
  have hfun : sechMomentumCurrent D = sechQuantumStress D := by
    funext y
    exact sechMomentumCurrent_eq D y
  rw [hfun]
  exact hasDerivAt_sechQuantumStress D x

theorem hasDerivAt_stationaryMassCurrent_time (D t x : ℝ) :
    HasDerivAt (fun _ : ℝ => sechMassCurrent D x) 0 t := by
  exact hasDerivAt_const t (sechMassCurrent D x)

/-- Equation (52): closed stationary continuity equation for the `sech` curvature fluid. -/
theorem sechContinuityEquation (D t x : ℝ) :
    (0 : ℝ) + 0 = 0 ∧
      HasDerivAt (fun _ : ℝ => sechDensity x) 0 t ∧
      HasDerivAt (sechMassCurrent D) 0 x := by
  exact ⟨by ring, hasDerivAt_const t (sechDensity x), hasDerivAt_sechMassCurrent D x⟩

/-- Equation (56): closed stationary momentum balance with certified derivatives on both sides. -/
theorem sechMomentumEquation (D t x : ℝ) :
    (0 : ℝ) + sechMomentumDerivative D x = sechMomentumDerivative D x ∧
      HasDerivAt (fun _ : ℝ => sechMassCurrent D x) 0 t ∧
      HasDerivAt (sechMomentumCurrent D) (sechMomentumDerivative D x) x ∧
      HasDerivAt (sechQuantumStress D) (sechMomentumDerivative D x) x := by
  exact ⟨by ring, hasDerivAt_stationaryMassCurrent_time D t x,
    hasDerivAt_sechMomentumCurrent D x, hasDerivAt_sechQuantumStress D x⟩

/-- The Bohm term `κ''/κ` for the corpus `sech` curvature. -/
noncomputable def sechBohmTerm (x : ℝ) : ℝ := solitonA2 x / solitonA x

theorem sechBohmTerm_eq (x : ℝ) : sechBohmTerm x = 1 - 2 * solitonQ x := by
  have hA0 : solitonA x ≠ 0 := (solitonA_pos x).ne'
  rw [sechBohmTerm, solitonA2]
  field_simp
  rw [← solitonA_sq]
  ring

/-- Closed form of `ρ + 2B`, the hydrodynamic potential in equation (53). -/
theorem sechHydrodynamicPotential_eq (x : ℝ) :
    sechDensity x + 2 * sechBohmTerm x = 2 - 3 * solitonQ x := by
  rw [sechDensity_eq, sechBohmTerm_eq]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
