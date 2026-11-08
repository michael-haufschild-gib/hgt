import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPoleClearing

/-!
# Entire numerators for averaged scalar Mellin transforms

Removing the universal Eisenstein pole from the horocycle constant term
produces an entire numerator. It equals one at the main pole and stays
nonzero at every arithmetic resonance, at every positive target height.
-/

open Complex RHTower MeasureTheory Set
open GaloisForLFunctions.BlackHoleRingdown
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The entire constant term after removal of the Eisenstein pole. -/
def filledNumeratorMean (Y : Height) (u : ℂ) : ℂ :=
  (2 * u - 1) * (Y.val : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
    (1 + 2 * u) * xi (2 * u) * (Y.val : ℂ) ^ (1 / 2 - u)

theorem differentiable_filledNumeratorMean (Y : Height) :
    Differentiable ℂ (filledNumeratorMean Y) := by
  have hY : (Y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hp : Differentiable ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 + u)) :=
    fun u => (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 + u) u).const_cpow
      (Or.inl hY)
  have hm : Differentiable ℂ (fun u : ℂ => (Y.val : ℂ) ^ (1 / 2 - u)) :=
    fun u => (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => 1 / 2 - u) u).const_cpow
      (Or.inl hY)
  have ha : Differentiable ℂ (fun u : ℂ => 2 * u - 1) := by fun_prop
  have hb : Differentiable ℂ (fun u : ℂ => 1 + 2 * u) := by fun_prop
  have hc : Differentiable ℂ (fun u : ℂ => 2 * u) := by fun_prop
  exact ((ha.mul hp).mul differentiable_xi_shift).add
    ((hb.mul (xi_differentiable.comp hc)).mul hm)

theorem filledNumeratorMean_eq (Y : Height) {u : ℂ} (hu : 2 * u - 1 ≠ 0) :
    filledNumeratorMean Y u = (2 * u - 1) * numeratorMean u Y := by
  rw [filledNumeratorMean, numeratorMean]
  field_simp [hu]

theorem filledNumeratorMean_half (Y : Height) :
    filledNumeratorMean Y (1 / 2) = 1 := by
  norm_num [filledNumeratorMean, xi_one]

theorem filledNumeratorMean_zero (Y : Height) : filledNumeratorMean Y 0 = 0 := by
  norm_num [filledNumeratorMean, xi_one, xi_zero]
  ring

/-- Every arithmetic resonance survives in the entire averaged numerator. -/
theorem filledNumeratorMean_ne_zero (p : Resonance) (Y : Height) :
    filledNumeratorMean Y p.val ≠ 0 := by
  have hr := re_neg_of_xi_shift_eq_zero p.property
  have htwo : 2 * p.val - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith only [hr, h']
  rw [filledNumeratorMean_eq Y htwo]
  exact mul_ne_zero htwo (numeratorMean_ne_zero p Y)

/-- The averaged Mellin transform with its universal double pole removed. -/
def narainMeanMainPoleNumerator (Y Z : Height) (u : ℂ) : ℂ :=
  filledNumeratorMean Y u * filledNumeratorMean Z u /
    (2 * (u * (1 + 2 * u)) * xi (1 + 2 * u))

theorem narainMeanMainPoleNumerator_eq (Y Z : Height) {u : ℂ}
    (hu : 2 * u - 1 ≠ 0) :
    narainMeanMainPoleNumerator Y Z u = (u - 1 / 2) ^ 2 * narainMellinMean Y Z u := by
  rw [narainMeanMainPoleNumerator, filledNumeratorMean_eq Y hu,
    filledNumeratorMean_eq Z hu, narainMellinMean, meanQuotient]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem narainMeanMainPoleNumerator_half (Y Z : Height) :
    narainMeanMainPoleNumerator Y Z (1 / 2) = 3 / (Real.pi : ℂ) := by
  rw [narainMeanMainPoleNumerator, filledNumeratorMean_half, filledNumeratorMean_half]
  norm_num
  calc
    (xi 2)⁻¹ * (1 / 2) = xi 1 / xi 2 := by rw [xi_one]; ring
    _ = _ := xi_one_div_xi_two

theorem narainMellinMean_cleared (Y Z : Height) {u : ℂ} (hu : 1 / 2 < u.re) :
    (u * (1 + 2 * u)) * xi (1 + 2 * u) *
      ((u - 1 / 2) ^ 2 * narainMellinMean Y Z u) =
      filledNumeratorMean Y u * filledNumeratorMean Z u / 2 := by
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
  rw [← narainMeanMainPoleNumerator_eq Y Z hminus, narainMeanMainPoleNumerator]
  have hc : u * (1 + 2 * u) ≠ 0 := mul_ne_zero hu0 hplus
  generalize u * (1 + 2 * u) = c at hc ⊢
  field_simp [hc, hD]

#print axioms differentiable_filledNumeratorMean
#print axioms filledNumeratorMean_ne_zero
#print axioms narainMellinMean_cleared
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
