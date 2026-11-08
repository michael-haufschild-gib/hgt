import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMellinContinuation
import GaloisForLFunctions.BlackHoleRingdown.TheReflectedSignalIsTheEchoTrain

/-!
# Clearing the universal scalar Mellin pole

Multiplication by `2u-1` removes the Eisenstein pole at `u=1/2`.
The resulting entire numerator has value one there and vanishes at zero.
Its product clears the scalar Mellin double pole without removing an
arithmetic resonance.
-/

open Complex RHTower MeasureTheory Set Filter Topology
open GaloisForLFunctions.BlackHoleRingdown

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The entire extension of `(2u-1)N(u,z)`. -/
def filledEisensteinNumerator (z : D4BMUpperHalfPlaneCoordinate) (u : ℂ) : ℂ :=
  (2 * u - 1) * (z.y : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
    (1 + 2 * u) * xi (2 * u) * (z.y : ℂ) ^ (1 / 2 - u) +
    (2 * u - 1) * (1 + 2 * u) * (2 * u) * eisTail u z.x z.y

theorem differentiable_filledEisensteinNumerator (z : D4BMUpperHalfPlaneCoordinate) :
    Differentiable ℂ (filledEisensteinNumerator z) := by
  have hY : (z.y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.y_pos.ne'
  have hp : Differentiable ℂ (fun u : ℂ => (z.y : ℂ) ^ (1 / 2 + u)) :=
    fun u => (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 + u) u).const_cpow
      (Or.inl hY)
  have hm : Differentiable ℂ (fun u : ℂ => (z.y : ℂ) ^ (1 / 2 - u)) :=
    fun u => (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 - u) u).const_cpow
      (Or.inl hY)
  have ha : Differentiable ℂ (fun u : ℂ => 2 * u - 1) := by fun_prop
  have hb : Differentiable ℂ (fun u : ℂ => 1 + 2 * u) := by fun_prop
  have hc : Differentiable ℂ (fun u : ℂ => 2 * u) := by fun_prop
  have hxi := xi_differentiable.comp hc
  have ht : Differentiable ℂ (fun u => eisTail u z.x z.y) :=
    fun u => differentiableAt_eisTail z.x z.y_pos u
  exact (((ha.mul hp).mul differentiable_xi_shift).add
    ((hb.mul hxi).mul hm)).add (((ha.mul hb).mul hc).mul ht)

theorem filledEisensteinNumerator_eq (z : D4BMUpperHalfPlaneCoordinate)
    {u : ℂ} (hu : 2 * u - 1 ≠ 0) :
    filledEisensteinNumerator z u = (2 * u - 1) * eisensteinNumerator u z.x z.y := by
  rw [filledEisensteinNumerator, eisensteinNumerator]
  field_simp [hu]

theorem filledEisensteinNumerator_zero (z : D4BMUpperHalfPlaneCoordinate) :
    filledEisensteinNumerator z 0 = 0 := by
  norm_num [filledEisensteinNumerator, xi_one, xi_zero]
  ring

theorem filledEisensteinNumerator_half (z : D4BMUpperHalfPlaneCoordinate) :
    filledEisensteinNumerator z (1 / 2) = 1 := by
  norm_num [filledEisensteinNumerator, xi_one]

/-- The scalar Mellin transform with its universal double pole removed. -/
def narainMainPoleNumerator (ρ σ : D4BMUpperHalfPlaneCoordinate) (u : ℂ) : ℂ :=
  filledEisensteinNumerator ρ u * filledEisensteinNumerator σ u /
    (2 * (u * (1 + 2 * u)) * xi (1 + 2 * u))

theorem analyticAt_narainMainPoleNumerator_half (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    AnalyticAt ℂ (narainMainPoleNumerator ρ σ) (1 / 2) := by
  have hc : AnalyticAt ℂ (fun u : ℂ => 2 * (u * (1 + 2 * u))) (1 / 2) := by
    fun_prop
  exact (((differentiable_filledEisensteinNumerator ρ).analyticAt (1 / 2)).mul
    ((differentiable_filledEisensteinNumerator σ).analyticAt (1 / 2))).div
      (hc.mul (differentiable_xi_shift.analyticAt (1 / 2))) (by norm_num [xi_two_ne_zero])

theorem narainMainPoleNumerator_half (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    narainMainPoleNumerator ρ σ (1 / 2) = 3 / (Real.pi : ℂ) := by
  rw [narainMainPoleNumerator, filledEisensteinNumerator_half,
    filledEisensteinNumerator_half]
  norm_num
  calc
    (xi 2)⁻¹ * (1 / 2) = xi 1 / xi 2 := by rw [xi_one]; ring
    _ = _ := xi_one_div_xi_two

theorem narainMainPoleNumerator_eq (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {u : ℂ} (hu : 2 * u - 1 ≠ 0) :
    narainMainPoleNumerator ρ σ u =
      (u - 1 / 2) ^ 2 * narainMellinContinuation ρ σ u := by
  rw [narainMainPoleNumerator, filledEisensteinNumerator_eq ρ hu,
    filledEisensteinNumerator_eq σ hu, narainMellinContinuation, productQuotient]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Clearing the main pole and arithmetic denominator in the actual Mellin identity. -/
theorem narainScalarHeat_mellin_cleared (ρ σ : D4BMUpperHalfPlaneCoordinate)
    {u : ℂ} (hu : 1 / 2 < u.re) :
    (u * (1 + 2 * u)) * xi (1 + 2 * u) *
        ((u - 1 / 2) ^ 2 * mellin (narainScalarHeat ρ σ) (1 / 2 + u)) =
      filledEisensteinNumerator ρ u * filledEisensteinNumerator σ u / 2 := by
  have hs : 1 < (1 / 2 + u).re := by simp; linarith only [hu]
  have hD : xi (1 + 2 * u) ≠ 0 :=
    xi_ne_zero_of_one_le_re (by simp; linarith only [hu])
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at hu
  have hplus : 1 + 2 * u ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hu, hr]
  have hminus : 2 * u - 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith only [hu, hr]
  have heq := narainMellinContinuation_eq_mellin ρ σ hs
  rw [show (1 / 2 + u) - 1 / 2 = u by ring] at heq
  rw [← heq, ← narainMainPoleNumerator_eq ρ σ hminus, narainMainPoleNumerator]
  have hc : u * (1 + 2 * u) ≠ 0 := mul_ne_zero hu0 hplus
  generalize u * (1 + 2 * u) = c at hc ⊢
  field_simp [hc, hD]

/-- The coefficient of the universal double pole is independent of both targets. -/
theorem tendsto_narainMellin_mainPole (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    Tendsto (fun u : ℂ => (u - 1 / 2) ^ 2 * narainMellinContinuation ρ σ u)
      (𝓝[≠] (1 / 2)) (𝓝 (3 / (Real.pi : ℂ))) := by
  have ht := (analyticAt_narainMainPoleNumerator_half ρ σ).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (1 / 2 : ℂ) ≤ 𝓝 (1 / 2))
  rw [narainMainPoleNumerator_half] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : 2 * u - 1 ≠ 0 := by
    intro h
    apply hu
    change u = 1 / 2
    linear_combination h / 2
  exact narainMainPoleNumerator_eq ρ σ hu'

#print axioms differentiable_filledEisensteinNumerator
#print axioms filledEisensteinNumerator_zero
#print axioms narainScalarHeat_mellin_cleared
#print axioms tendsto_narainMellin_mainPole

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
