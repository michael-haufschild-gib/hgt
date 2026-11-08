import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralZero
import GaloisForLFunctions.HTGeometry.AnalyticDoublePoleSplit

/-!
# The exact scalar Narain principal part

Two removable divided differences of the filled Mellin numerator separate
the universal double pole, the target-dependent simple pole and a
holomorphic remainder.
-/

open Complex RHTower Set
open GaloisForLFunctions.BlackHoleRingdown

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The domain where the main-pole numerator has no remaining denominator zero. -/
def narainMellinRegularDomain : Set ℂ :=
  {u | (1 + 2 * u) * xi (1 + 2 * u) ≠ 0}

/-- The exact constant associated with the scalar logarithmic main term. -/
def narainScalarConstant (ρ σ : D4BMUpperHalfPlaneCoordinate) : ℂ :=
  deriv (narainMainPoleNumerator ρ σ) (1 / 2)

/-- The holomorphic remainder after subtracting both principal terms. -/
def narainMellinRegularPart (ρ σ : D4BMUpperHalfPlaneCoordinate) : ℂ → ℂ :=
  slopeExt (slopeExt (narainMainPoleNumerator ρ σ) (1 / 2)) (1 / 2)

private theorem differentiable_reducedDenominator :
    Differentiable ℂ (fun u : ℂ => (1 + 2 * u) * xi (1 + 2 * u)) :=
  (by fun_prop : Differentiable ℂ (fun u : ℂ => 1 + 2 * u)).mul
    differentiable_xi_shift

theorem isOpen_narainMellinRegularDomain : IsOpen narainMellinRegularDomain :=
  isOpen_ne_fun differentiable_reducedDenominator.continuous continuous_const

theorem half_mem_narainMellinRegularDomain : (1 / 2 : ℂ) ∈ narainMellinRegularDomain := by
  norm_num [narainMellinRegularDomain, xi_two_ne_zero]

theorem differentiableOn_narainMainPoleNumerator (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    DifferentiableOn ℂ (narainMainPoleNumerator ρ σ) narainMellinRegularDomain :=
  fun _ hu => (analyticAt_narainMainPoleNumerator ρ σ hu).differentiableAt.differentiableWithinAt

theorem differentiableOn_narainMellinRegularPart (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    DifferentiableOn ℂ (narainMellinRegularPart ρ σ) narainMellinRegularDomain :=
  differentiableOn_slopeExt isOpen_narainMellinRegularDomain
    (differentiableOn_slopeExt isOpen_narainMellinRegularDomain
      (differentiableOn_narainMainPoleNumerator ρ σ) half_mem_narainMellinRegularDomain)
    half_mem_narainMellinRegularDomain

/-- Exact principal-part subtraction, including the target-dependent simple pole. -/
theorem narainMellinContinuation_principalPart (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {u : ℂ} (hu : u ≠ 1 / 2) :
    narainMellinContinuation ρ σ u =
      (3 / (Real.pi : ℂ)) / (u - 1 / 2) ^ 2 +
        narainScalarConstant ρ σ / (u - 1 / 2) + narainMellinRegularPart ρ σ u := by
  have h₁ := eq_add_mul_slopeExt (f := narainMainPoleNumerator ρ σ) hu
  have h₂ := eq_add_mul_slopeExt (f := slopeExt (narainMainPoleNumerator ρ σ) (1 / 2)) hu
  rw [slopeExt_self] at h₂
  rw [h₂, narainMainPoleNumerator_half] at h₁
  have hw : u - 1 / 2 ≠ 0 := sub_ne_zero.mpr hu
  have htwo : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h / 2
  calc
    _ = narainMainPoleNumerator ρ σ u / (u - 1 / 2) ^ 2 := by
      apply (eq_div_iff (pow_ne_zero 2 hw)).mpr
      rw [narainMainPoleNumerator_eq ρ σ htwo]
      ring
    _ = _ := by
      rw [h₁]
      unfold narainScalarConstant narainMellinRegularPart
      generalize u - 1 / 2 = w at hw ⊢
      field_simp [hw]
      ring

/-- The simple-pole coefficient in terms of the two target derivatives and the xi derivative. -/
theorem narainScalarConstant_eq (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    narainScalarConstant ρ σ = (3 / (Real.pi : ℂ)) *
      (deriv (filledEisensteinNumerator ρ) (1 / 2) +
        deriv (filledEisensteinNumerator σ) (1 / 2) - 3 -
          2 * deriv xi 2 / xi 2) := by
  have hlin := ((hasDerivAt_id (1 / 2 : ℂ)).const_mul 2).const_add 1
  have hpoly := ((hasDerivAt_id (1 / 2 : ℂ)).mul hlin).const_mul 2
  have hxi := (xi_differentiable (1 + 2 * (1 / 2 : ℂ))).hasDerivAt.comp
    (1 / 2) hlin
  have hn := ((differentiable_filledEisensteinNumerator ρ) (1 / 2)).hasDerivAt.mul
    ((differentiable_filledEisensteinNumerator σ) (1 / 2)).hasDerivAt
  have hd := hpoly.mul hxi
  have hquot := hn.div hd (by norm_num [xi_two_ne_zero])
  have heq := hquot.deriv
  change narainScalarConstant ρ σ = _ at heq
  rw [heq, ← xi_one_div_xi_two, xi_one]
  norm_num [filledEisensteinNumerator_half]
  field_simp [xi_two_ne_zero]
  ring

#print axioms differentiableOn_narainMellinRegularPart
#print axioms narainMellinContinuation_principalPart
#print axioms narainScalarConstant_eq

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
