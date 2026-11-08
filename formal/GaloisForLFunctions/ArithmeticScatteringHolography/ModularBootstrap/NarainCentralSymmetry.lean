import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart

/-!
# Central reflection and first jets

The xi functional equation gives odd filled target numerators, even divided numerators, and their first and third central jet relations.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The xi functional equation makes each filled constant term odd at the Mellin center. -/
theorem filledNumeratorMean_neg (Y : Height) (u : ℂ) :
    filledNumeratorMean Y (-u) = -filledNumeratorMean Y u := by
  unfold filledNumeratorMean
  rw [show 1 + 2 * (-u) = 1 - 2 * u by ring, xi_one_sub,
    show 2 * (-u) = 1 - (1 + 2 * u) by ring, xi_one_sub,
    show (1 / 2 : ℂ) + (-u) = 1 / 2 - u by ring,
    show (1 / 2 : ℂ) - (-u) = 1 / 2 + u by ring]
  ring

/-- Dividing out the universal central zero leaves an entire even function. -/
theorem dividedFilledNumeratorMean_neg (Y : Height) (u : ℂ) :
    dividedFilledNumeratorMean Y (-u) = dividedFilledNumeratorMean Y u := by
  by_cases hu : u = 0
  · subst u
    rw [neg_zero]
  · have h := filledNumeratorMean_neg Y u
    rw [filledNumeratorMean_eq_mul_divided, filledNumeratorMean_eq_mul_divided] at h
    simp only [neg_mul, neg_inj] at h
    exact mul_left_cancel₀ hu h

private theorem xi_deriv_zero_eq_neg_one : deriv xi 0 = -deriv xi 1 := by
  have he : (fun z : ℂ => xi (1 - z)) = xi := funext xi_one_sub
  have h : deriv (fun z : ℂ => xi (1 - z)) 1 = -deriv xi (1 - 1) := by
    rw [deriv_comp_const_sub]
  rw [he, sub_self] at h
  linear_combination h

/-- The first central jet isolates the unique exceptional target height. -/
theorem filledNumeratorMean_deriv_zero (Y : Height) :
    deriv (filledNumeratorMean Y) 0 =
      (Y.val : ℂ) ^ (1 / 2 : ℂ) * (2 - 4 * deriv xi 1 - Complex.log (Y.val : ℂ)) := by
  have hY : (Y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hlin := (hasDerivAt_id (0 : ℂ)).const_mul 2
  have ha := hlin.sub_const 1
  have hb := hlin.const_add 1
  have hp := ((hasDerivAt_id (0 : ℂ)).const_add (1 / 2)).const_cpow
    (c := (Y.val : ℂ)) (Or.inl hY)
  have hm := ((hasDerivAt_id (0 : ℂ)).const_sub (1 / 2)).const_cpow
    (c := (Y.val : ℂ)) (Or.inl hY)
  have hxi := (xi_differentiable (1 + 2 * (0 : ℂ))).hasDerivAt.comp 0 hb
  have hxj := (xi_differentiable (2 * (0 : ℂ))).hasDerivAt.comp 0 hlin
  have h := (((ha.mul hp).mul hxi).add ((hb.mul hxj).mul hm)).deriv
  change deriv (filledNumeratorMean Y) 0 = _ at h
  rw [h]
  norm_num [xi_one, xi_zero, xi_deriv_zero_eq_neg_one]
  ring

/-- The divided numerator evaluates to the first jet at the removed zero. -/
theorem filledNumeratorMean_first_jet_eq_divided (Y : Height) :
    deriv (filledNumeratorMean Y) 0 = dividedFilledNumeratorMean Y 0 := by
  have heq : filledNumeratorMean Y = fun u => u * dividedFilledNumeratorMean Y u :=
    funext (filledNumeratorMean_eq_mul_divided Y)
  rw [heq]
  have h := ((hasDerivAt_id (0 : ℂ)).mul
    ((differentiable_dividedFilledNumeratorMean Y) 0).hasDerivAt).deriv
  change deriv (fun u : ℂ => u * dividedFilledNumeratorMean Y u) 0 =
    1 * dividedFilledNumeratorMean Y 0 + 0 * deriv (dividedFilledNumeratorMean Y) 0 at h
  simpa only [one_mul, zero_mul, add_zero] using h

/-- Evenness removes the first central jet of each divided target numerator. -/
theorem dividedFilledNumeratorMean_first_jet_zero (Y : Height) :
    iteratedDeriv 1 (dividedFilledNumeratorMean Y) 0 = 0 := by
  have heq : (fun u : ℂ => dividedFilledNumeratorMean Y (-u)) = dividedFilledNumeratorMean Y :=
    funext (dividedFilledNumeratorMean_neg Y)
  have h := congrArg (fun f : ℂ → ℂ => iteratedDeriv 1 f 0) heq
  rw [_root_.iteratedDeriv_comp_neg] at h
  simp only [neg_zero, pow_one, smul_eq_mul, neg_one_mul] at h
  linear_combination -h / 2

/-- Dividing out the universal zero converts the cubic jet to three times the second jet. -/
theorem filledNumeratorMean_third_jet_eq_divided (Y : Height) :
    iteratedDeriv 3 (filledNumeratorMean Y) 0 =
      3 * iteratedDeriv 2 (dividedFilledNumeratorMean Y) 0 := by
  have heq : filledNumeratorMean Y = fun u => u * dividedFilledNumeratorMean Y u :=
    funext (filledNumeratorMean_eq_mul_divided Y)
  rw [heq, iteratedDeriv_fun_mul (by fun_prop)
    ((differentiable_dividedFilledNumeratorMean Y).analyticAt 0).contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id]

#print axioms filledNumeratorMean_neg
#print axioms dividedFilledNumeratorMean_neg
#print axioms filledNumeratorMean_deriv_zero
#print axioms filledNumeratorMean_first_jet_eq_divided
#print axioms dividedFilledNumeratorMean_first_jet_zero
#print axioms filledNumeratorMean_third_jet_eq_divided
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
