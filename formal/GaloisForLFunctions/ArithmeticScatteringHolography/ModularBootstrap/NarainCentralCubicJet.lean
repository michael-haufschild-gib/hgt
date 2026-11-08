import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart

/-!
# Cubic jets of the filled Narain numerator

Reflection reduces the filled numerator to one exponential xi factor. Exact product differentiation gives its cubic jet and the exceptional-height specialization.
-/

open Complex RHTower
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem xi_affine_jet (n : ℕ) :
    iteratedDeriv n (fun u : ℂ => xi (1 + 2 * u)) 0 = 2 ^ n * iteratedDeriv n xi 1 := by
  have hc : ContDiff ℂ n (fun u : ℂ => xi (1 + u)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    have h : AnalyticAt ℂ (fun v : ℂ => xi (1 + v)) u :=
      (xi_differentiable.analyticAt (1 + u)).comp (by fun_prop)
    exact h.contDiffAt
  change iteratedDeriv n (fun u : ℂ => (fun v : ℂ => xi (1 + v)) (2 * u)) 0 = _
  rw [iteratedDeriv_comp_const_mul hc, iteratedDeriv_comp_const_add]
  simp only [mul_zero, add_zero]

private theorem third_jet_linear_mul (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    iteratedDeriv 3 (fun u : ℂ => (1 - 2 * u) * f u) 0 =
      iteratedDeriv 3 f 0 - 6 * iteratedDeriv 2 f 0 := by
  have hl : AnalyticAt ℂ (fun u : ℂ => 1 - 2 * u) 0 := by fun_prop
  have hd : deriv (fun u : ℂ => 1 - 2 * u) = fun _ => -2 := by
    funext u
    simpa only [id, mul_one] using (((hasDerivAt_id u).const_mul 2).const_sub 1).deriv
  rw [iteratedDeriv_fun_mul hl.contDiffAt (hf.analyticAt 0).contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ', hd]
  ring

/-- The cubic jet of the reflected xi factor, before specializing the exceptional height. -/
theorem narainCentralFactor_third_jet (a : ℂ) :
    iteratedDeriv 3 (fun u : ℂ => (1 - 2 * u) *
      (Complex.exp (a * u) * xi (1 + 2 * u))) 0 =
      (a ^ 3 - 6 * a ^ 2) / 2 +
        (6 * a ^ 2 - 24 * a) * deriv xi 1 +
          (12 * a - 24) * deriv (deriv xi) 1 + 8 * deriv (deriv (deriv xi)) 1 := by
  have hE : Differentiable ℂ (fun u : ℂ => Complex.exp (a * u)) := by fun_prop
  have hX : Differentiable ℂ (fun u : ℂ => xi (1 + 2 * u)) := differentiable_xi_shift
  have hH : Differentiable ℂ (fun u : ℂ => Complex.exp (a * u) * xi (1 + 2 * u)) := by
    convert! hE.mul hX using 1
  rw [third_jet_linear_mul _ hH]
  rw [iteratedDeriv_fun_mul (hE.analyticAt 0).contDiffAt (hX.analyticAt 0).contDiffAt,
    iteratedDeriv_fun_mul (hE.analyticAt 0).contDiffAt (hX.analyticAt 0).contDiffAt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [iteratedDeriv_cexp_const_mul, xi_affine_jet, mul_zero, Complex.exp_zero, mul_one]
  norm_num [iteratedDeriv_succ', xi_one]
  ring

/-- At the exceptional logarithmic height, the cubic jet has a short expression in xi jets. -/
theorem narainCentralFactor_exceptional_third_jet :
    iteratedDeriv 3 (fun u : ℂ => (1 - 2 * u) *
      (Complex.exp ((2 - 4 * deriv xi 1) * u) * xi (1 + 2 * u))) 0 =
      -8 + 64 * (deriv xi 1) ^ 3 -
        48 * deriv (deriv xi) 1 * deriv xi 1 + 8 * deriv (deriv (deriv xi)) 1 := by
  rw [narainCentralFactor_third_jet]
  ring

/-- Reflection expresses the filled target numerator as a skew difference of one entire factor. -/
theorem filledNumeratorMean_eq_skew (Y : Height) (u : ℂ) :
    filledNumeratorMean Y u = (Y.val : ℂ) ^ (1 / 2 : ℂ) *
      (((1 - 2 * (-u)) * (Complex.exp (Complex.log (Y.val : ℂ) * (-u)) * xi (1 + 2 * (-u)))) -
        ((1 - 2 * u) * (Complex.exp (Complex.log (Y.val : ℂ) * u) * xi (1 + 2 * u)))) := by
  have hY : (Y.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Y.property.ne'
  have hp (v : ℂ) : (Y.val : ℂ) ^ (1 / 2 + v) =
      (Y.val : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (Complex.log (Y.val : ℂ) * v) := by
    rw [Complex.cpow_add _ _ hY]
    congr 1
    exact Complex.cpow_def_of_ne_zero hY v
  have hxi : xi (2 * u) = xi (1 + 2 * (-u)) := by
    rw [show 1 + 2 * (-u) = 1 - 2 * u by ring, xi_one_sub]
  rw [filledNumeratorMean, hp, show (1 / 2 : ℂ) - u = 1 / 2 + (-u) by ring, hp, hxi]
  ring

/-- The actual filled numerator has an explicit third jet at the Mellin centre. -/
theorem filledNumeratorMean_third_jet (Y : Height) :
    iteratedDeriv 3 (filledNumeratorMean Y) 0 =
      -2 * (Y.val : ℂ) ^ (1 / 2 : ℂ) *
        ((Complex.log (Y.val : ℂ) ^ 3 - 6 * Complex.log (Y.val : ℂ) ^ 2) / 2 +
          (6 * Complex.log (Y.val : ℂ) ^ 2 - 24 * Complex.log (Y.val : ℂ)) * deriv xi 1 +
            (12 * Complex.log (Y.val : ℂ) - 24) * deriv (deriv xi) 1 +
              8 * deriv (deriv (deriv xi)) 1) := by
  let f : ℂ → ℂ := fun u => (1 - 2 * u) *
    (Complex.exp (Complex.log (Y.val : ℂ) * u) * xi (1 + 2 * u))
  have hf : Differentiable ℂ f := by
    exact (by fun_prop : Differentiable ℂ (fun u : ℂ => 1 - 2 * u)).mul
      ((by fun_prop : Differentiable ℂ (fun u : ℂ => Complex.exp (Complex.log (Y.val : ℂ) * u))).mul
        differentiable_xi_shift)
  have heq : filledNumeratorMean Y = fun u => (Y.val : ℂ) ^ (1 / 2 : ℂ) * (f (-u) - f u) :=
    funext (filledNumeratorMean_eq_skew Y)
  have hneg : Differentiable ℂ (fun u : ℂ => f (-u)) := hf.comp (by fun_prop)
  rw [heq, GaloisForLFunctions.iteratedDeriv_const_mul_field]
  change (Y.val : ℂ) ^ (1 / 2 : ℂ) *
    iteratedDeriv 3 (fun u : ℂ => f (-u) - f u) 0 = _
  rw [iteratedDeriv_fun_sub (hneg.analyticAt 0).contDiffAt (hf.analyticAt 0).contDiffAt,
    _root_.iteratedDeriv_comp_neg]
  simp only [neg_zero, smul_eq_mul]
  dsimp only [f]
  rw [narainCentralFactor_third_jet]
  ring

#print axioms narainCentralFactor_third_jet
#print axioms narainCentralFactor_exceptional_third_jet
#print axioms filledNumeratorMean_third_jet
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
