import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Central logarithmic xi jet

Differentiating the logarithmic derivative twice expresses the third logarithmic jet at one in ordinary xi derivatives.
-/

open Complex RHTower Filter Topology
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The third logarithmic xi jet at one, expressed through ordinary xi derivatives. -/
theorem narainCentralXiCurvature_eq :
    deriv (deriv (logDeriv xi)) (1 : ℂ) =
      2 * deriv (deriv (deriv xi)) 1 -
        12 * deriv (deriv xi) 1 * deriv xi 1 + 16 * (deriv xi 1) ^ 3 := by
  let R : ℂ → ℂ := fun z =>
    (deriv (deriv xi) z * xi z - deriv xi z * deriv xi z) / xi z ^ 2
  have hne : xi (1 : ℂ) ≠ 0 := by rw [xi_one]; norm_num
  have hlocal : deriv (logDeriv xi) =ᶠ[𝓝 (1 : ℂ)] R := by
    filter_upwards [(xi_differentiable.continuous.continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds hne))] with z hz
    have hξ := (xi_differentiable z).hasDerivAt
    have hξ' := (xi_differentiable.analyticAt z).deriv.differentiableAt.hasDerivAt
    have hq := hξ'.div hξ hz
    simpa only [logDeriv, R, Pi.div_apply, pow_two] using hq.deriv
  have hξ := (xi_differentiable (1 : ℂ)).hasDerivAt
  have hξ' := (xi_differentiable.analyticAt (1 : ℂ)).deriv.differentiableAt.hasDerivAt
  have hξ'' := (xi_differentiable.analyticAt (1 : ℂ)).deriv.deriv.differentiableAt.hasDerivAt
  have hnum := (hξ''.mul hξ).sub (hξ'.mul hξ')
  have hden := hξ.pow 2
  have hq := hnum.div hden (pow_ne_zero 2 hne)
  change HasDerivAt R _ 1 at hq
  rw [hlocal.deriv_eq, hq.deriv]
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, xi_one]
  ring

#print axioms narainCentralXiCurvature_eq
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
