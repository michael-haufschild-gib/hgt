import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Navier-Stokes viscosity scaling

This file formalizes the point-jet algebra of equation (10.22) in the supplied Navier-Stokes
paper.  Under `x ↦ x / √ν`, velocity and force acquire a factor `√ν`, pressure acquires
`ν`, first spatial velocity derivatives are unchanged, and Laplacians acquire `(√ν)⁻¹`.
Consequently every momentum-residual component acquires exactly the common factor `√ν`,
while divergence is invariant.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.NavierStokesViscosityScaling

/-- Pointwise value and derivative data for a forced, unsteady, dimension-`d` Navier-Stokes
field.  `spatialDerivative i k` represents `∂ₖ uᵢ`. -/
structure NavierStokesPointJet (d : ℕ) where
  velocity : Fin d → ℝ
  timeDerivative : Fin d → ℝ
  spatialDerivative : Fin d → Fin d → ℝ
  laplacian : Fin d → ℝ
  pressureGradient : Fin d → ℝ
  force : Fin d → ℝ

/-- Convective derivative `(u · ∇)uᵢ` represented by a point jet. -/
def advection {d : ℕ} (J : NavierStokesPointJet d) (i : Fin d) : ℝ :=
  ∑ k, J.velocity k * J.spatialDerivative i k

/-- Divergence represented by a point jet. -/
def divergence {d : ℕ} (J : NavierStokesPointJet d) : ℝ :=
  ∑ i, J.spatialDerivative i i

/-- Forced Navier-Stokes momentum residual at viscosity `ν`. -/
def momentumResidual {d : ℕ} (ν : ℝ) (J : NavierStokesPointJet d) (i : Fin d) : ℝ :=
  J.timeDerivative i + advection J i - ν * J.laplacian i +
    J.pressureGradient i - J.force i

/-- Pointwise incompressibility and momentum equations. -/
def SolvesAt {d : ℕ} (ν : ℝ) (J : NavierStokesPointJet d) : Prop :=
  divergence J = 0 ∧ ∀ i, momentumResidual ν J i = 0

/-- Derivative data induced by the spatial/amplitude viscosity scaling (10.22). -/
def viscosityRescaledJet {d : ℕ} (ν : ℝ) (J : NavierStokesPointJet d) :
    NavierStokesPointJet d where
  velocity i := Real.sqrt ν * J.velocity i
  timeDerivative i := Real.sqrt ν * J.timeDerivative i
  spatialDerivative i k := J.spatialDerivative i k
  laplacian i := (Real.sqrt ν)⁻¹ * J.laplacian i
  pressureGradient i := Real.sqrt ν * J.pressureGradient i
  force i := Real.sqrt ν * J.force i

/-- Advection acquires the common factor `√ν`. -/
theorem advection_viscosityRescaledJet {d : ℕ} (ν : ℝ)
    (J : NavierStokesPointJet d) (i : Fin d) :
    advection (viscosityRescaledJet ν J) i = Real.sqrt ν * advection J i := by
  simp [advection, viscosityRescaledJet, Finset.mul_sum, mul_assoc]

/-- Divergence is unchanged by the viscosity scaling. -/
theorem divergence_viscosityRescaledJet {d : ℕ} (ν : ℝ)
    (J : NavierStokesPointJet d) :
    divergence (viscosityRescaledJet ν J) = divergence J := by
  rfl

/-- **Equation (10.22), residual form.** The viscosity-`ν` residual of the scaled jet is
`√ν` times the viscosity-one residual. -/
theorem momentumResidual_viscosityRescaledJet {d : ℕ} {ν : ℝ} (hν : 0 < ν)
    (J : NavierStokesPointJet d) (i : Fin d) :
    momentumResidual ν (viscosityRescaledJet ν J) i =
      Real.sqrt ν * momentumResidual 1 J i := by
  have hs : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.2 hν).ne'
  have hratio : ν * (Real.sqrt ν)⁻¹ = Real.sqrt ν := by
    calc
      ν * (Real.sqrt ν)⁻¹ = (Real.sqrt ν) ^ (2 : ℕ) * (Real.sqrt ν)⁻¹ := by
        rw [Real.sq_sqrt hν.le]
      _ = Real.sqrt ν := by field_simp
  rw [momentumResidual, advection_viscosityRescaledJet, momentumResidual]
  simp only [viscosityRescaledJet]
  rw [← mul_assoc ν, hratio]
  ring

/-- Every viscosity-one point solution transfers to arbitrary positive viscosity. -/
theorem solvesAt_viscosityRescaledJet {d : ℕ} {ν : ℝ} (hν : 0 < ν)
    {J : NavierStokesPointJet d} (hJ : SolvesAt 1 J) :
    SolvesAt ν (viscosityRescaledJet ν J) := by
  constructor
  · rw [divergence_viscosityRescaledJet]
    exact hJ.1
  · intro i
    rw [momentumResidual_viscosityRescaledJet hν, hJ.2 i, mul_zero]

/-- Pointwise kinetic-energy density. -/
def kineticDensity {d : ℕ} (J : NavierStokesPointJet d) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, J.velocity i ^ (2 : ℕ)

/-- Velocity amplitude scaling multiplies kinetic-energy density by `ν`. -/
theorem kineticDensity_viscosityRescaledJet {d : ℕ} {ν : ℝ} (hν : 0 ≤ ν)
    (J : NavierStokesPointJet d) :
    kineticDensity (viscosityRescaledJet ν J) = ν * kineticDensity J := by
  unfold kineticDensity
  simp only [viscosityRescaledJet]
  have hsqrt : (Real.sqrt ν) ^ (2 : ℕ) = ν := Real.sq_sqrt hν
  calc
    (1 / 2 : ℝ) * ∑ i, (Real.sqrt ν * J.velocity i) ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ∑ i, ν * J.velocity i ^ (2 : ℕ) := by
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [mul_pow, hsqrt]
    _ = ν * ((1 / 2 : ℝ) * ∑ i, J.velocity i ^ (2 : ℕ)) := by
      rw [← Finset.mul_sum]
      ring

/-- Point-jet data induced by the fixed-viscosity parabolic rescaling used in Corollary 10.6:
space has scale `scale`, time has scale `scale²`, velocity has scale `scale`, pressure has
scale `scale²`, and force has scale `scale³`. -/
def parabolicRescaledJet {d : ℕ} (scale : ℝ) (J : NavierStokesPointJet d) :
    NavierStokesPointJet d where
  velocity i := scale * J.velocity i
  timeDerivative i := scale ^ (3 : ℕ) * J.timeDerivative i
  spatialDerivative i k := scale ^ (2 : ℕ) * J.spatialDerivative i k
  laplacian i := scale ^ (3 : ℕ) * J.laplacian i
  pressureGradient i := scale ^ (3 : ℕ) * J.pressureGradient i
  force i := scale ^ (3 : ℕ) * J.force i

/-- Parabolic rescaling multiplies advection by `scale³`. -/
theorem advection_parabolicRescaledJet {d : ℕ} (scale : ℝ)
    (J : NavierStokesPointJet d) (i : Fin d) :
    advection (parabolicRescaledJet scale J) i = scale ^ (3 : ℕ) * advection J i := by
  unfold advection
  simp only [parabolicRescaledJet]
  calc
    ∑ k, (scale * J.velocity k) * (scale ^ (2 : ℕ) * J.spatialDerivative i k) =
        ∑ k, scale ^ (3 : ℕ) * (J.velocity k * J.spatialDerivative i k) := by
      apply sum_congr rfl
      intro k hk
      ring
    _ = scale ^ (3 : ℕ) * ∑ k, J.velocity k * J.spatialDerivative i k := by
      rw [Finset.mul_sum]

/-- Parabolic rescaling multiplies divergence by `scale²`. -/
theorem divergence_parabolicRescaledJet {d : ℕ} (scale : ℝ)
    (J : NavierStokesPointJet d) :
    divergence (parabolicRescaledJet scale J) = scale ^ (2 : ℕ) * divergence J := by
  unfold divergence
  simp only [parabolicRescaledJet]
  rw [Finset.mul_sum]

/-- Fixed-viscosity Navier-Stokes momentum residual is parabolically homogeneous of degree
three. -/
theorem momentumResidual_parabolicRescaledJet {d : ℕ} (ν scale : ℝ)
    (J : NavierStokesPointJet d) (i : Fin d) :
    momentumResidual ν (parabolicRescaledJet scale J) i =
      scale ^ (3 : ℕ) * momentumResidual ν J i := by
  rw [momentumResidual, advection_parabolicRescaledJet, momentumResidual]
  simp only [parabolicRescaledJet]
  ring

/-- Parabolic rescaling preserves the pointwise Navier-Stokes equations at fixed viscosity. -/
theorem solvesAt_parabolicRescaledJet {d : ℕ} {ν scale : ℝ}
    {J : NavierStokesPointJet d} (hJ : SolvesAt ν J) :
    SolvesAt ν (parabolicRescaledJet scale J) := by
  constructor
  · rw [divergence_parabolicRescaledJet, hJ.1, mul_zero]
  · intro i
    rw [momentumResidual_parabolicRescaledJet, hJ.2 i, mul_zero]

/-- Parabolic velocity scaling multiplies pointwise kinetic density by `scale²`. -/
theorem kineticDensity_parabolicRescaledJet {d : ℕ} (scale : ℝ)
    (J : NavierStokesPointJet d) :
    kineticDensity (parabolicRescaledJet scale J) = scale ^ (2 : ℕ) * kineticDensity J := by
  unfold kineticDensity
  simp only [parabolicRescaledJet]
  calc
    (1 / 2 : ℝ) * ∑ i, (scale * J.velocity i) ^ (2 : ℕ) =
        (1 / 2 : ℝ) * ∑ i, scale ^ (2 : ℕ) * J.velocity i ^ (2 : ℕ) := by
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [mul_pow]
    _ = scale ^ (2 : ℕ) * ((1 / 2 : ℝ) * ∑ i, J.velocity i ^ (2 : ℕ)) := by
      rw [← Finset.mul_sum]
      ring

end GaloisForLFunctions.HTGeometry.NavierStokesViscosityScaling
