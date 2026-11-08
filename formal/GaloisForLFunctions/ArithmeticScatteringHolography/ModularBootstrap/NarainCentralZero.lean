import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPoleClearing
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# The universal scalar Narain zero at half

Each filled Eisenstein numerator vanishes at zero. Its entire divided
difference removes the apparent denominator there, leaving a universal
zero of the scalar Mellin continuation at `s=1/2`.
-/

open Complex RHTower Set Filter Topology
open GaloisForLFunctions.BlackHoleRingdown

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The entire quotient of the filled numerator by its universal zero. -/
def dividedFilledEisensteinNumerator (z : D4BMUpperHalfPlaneCoordinate) : ℂ → ℂ :=
  dslope (filledEisensteinNumerator z) 0

theorem differentiable_dividedFilledEisensteinNumerator (z : D4BMUpperHalfPlaneCoordinate) :
    Differentiable ℂ (dividedFilledEisensteinNumerator z) := by
  intro u
  exact (analyticAt_dslope_of_analyticAt
    ((differentiable_filledEisensteinNumerator z).analyticAt 0)
    ((differentiable_filledEisensteinNumerator z).analyticAt u)).differentiableAt

theorem filledEisensteinNumerator_eq_mul_divided
    (z : D4BMUpperHalfPlaneCoordinate) (u : ℂ) :
    filledEisensteinNumerator z u = u * dividedFilledEisensteinNumerator z u := by
  by_cases hu : u = 0
  · subst u
    simp only [filledEisensteinNumerator_zero, zero_mul]
  · rw [dividedFilledEisensteinNumerator, dslope_of_ne _ hu, slope_def_field,
      filledEisensteinNumerator_zero, sub_zero, sub_zero, mul_div_cancel₀ _ hu]

/-- The main-pole numerator with its apparent central singularity removed. -/
def narainReducedMainPoleNumerator (ρ σ : D4BMUpperHalfPlaneCoordinate) (u : ℂ) : ℂ :=
  u * dividedFilledEisensteinNumerator ρ u * dividedFilledEisensteinNumerator σ u /
    (2 * (1 + 2 * u) * xi (1 + 2 * u))

theorem narainMainPoleNumerator_eq_reduced (ρ σ : D4BMUpperHalfPlaneCoordinate) (u : ℂ) :
    narainMainPoleNumerator ρ σ u = narainReducedMainPoleNumerator ρ σ u := by
  by_cases hu : u = 0
  · subst u
    simp [narainMainPoleNumerator, narainReducedMainPoleNumerator]
  · rw [narainMainPoleNumerator, filledEisensteinNumerator_eq_mul_divided ρ,
      filledEisensteinNumerator_eq_mul_divided σ, narainReducedMainPoleNumerator]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp [hu]

/-- Only the arithmetic denominator and the endpoint `u=-1/2` remain. -/
theorem analyticAt_narainMainPoleNumerator (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {u : ℂ} (hu : (1 + 2 * u) * xi (1 + 2 * u) ≠ 0) :
    AnalyticAt ℂ (narainMainPoleNumerator ρ σ) u := by
  have heq : narainMainPoleNumerator ρ σ = narainReducedMainPoleNumerator ρ σ :=
    funext (narainMainPoleNumerator_eq_reduced ρ σ)
  rw [heq]
  have hn := (differentiable_id.mul (differentiable_dividedFilledEisensteinNumerator ρ)).mul
    (differentiable_dividedFilledEisensteinNumerator σ)
  have hd := (by fun_prop : Differentiable ℂ (fun u : ℂ => 2 * (1 + 2 * u))).mul
    differentiable_xi_shift
  exact (hn.analyticAt u).div (hd.analyticAt u) (by
    rw [mul_assoc]
    exact mul_ne_zero two_ne_zero hu)

theorem narainMainPoleNumerator_zero (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    narainMainPoleNumerator ρ σ 0 = 0 := by
  simp [narainMainPoleNumerator]

/-- The apparent pole at `s=1/2` is removable for every target pair. -/
theorem analyticAt_narainMellinContinuation_zero (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    AnalyticAt ℂ (narainMellinContinuation ρ σ) 0 := by
  have ha := analyticAt_narainMainPoleNumerator ρ σ (u := 0) (by norm_num [xi_one])
  have hd : AnalyticAt ℂ (fun u : ℂ => (u - 1 / 2) ^ 2) 0 := by fun_prop
  have hq := ha.div hd (by norm_num)
  apply hq.congr
  filter_upwards [isOpen_ne.mem_nhds (show (0 : ℂ) ≠ 1 / 2 by norm_num)] with u hu
  have htwo : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    linear_combination h / 2
  symm
  apply (eq_div_iff (pow_ne_zero 2 (sub_ne_zero.mpr hu))).mpr
  rw [narainMainPoleNumerator_eq ρ σ htwo]
  ring

theorem narainMellinContinuation_zero (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    narainMellinContinuation ρ σ 0 = 0 := by
  simp [narainMellinContinuation]

#print axioms narainMainPoleNumerator_eq_reduced
#print axioms analyticAt_narainMainPoleNumerator
#print axioms analyticAt_narainMellinContinuation_zero
#print axioms narainMellinContinuation_zero

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
