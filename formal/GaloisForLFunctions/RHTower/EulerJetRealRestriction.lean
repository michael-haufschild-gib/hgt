import GaloisForLFunctions.HTGeometry.EulerOrdinaryJetChange
import GaloisForLFunctions.RHTower.BarnesMellinEulerDerivative

/-!
# The Euler jets of a complex function, read on the real axis

The Euler operator `x d/dx` on the restriction of a complex-analytic function to the real axis is
the restriction of the complex Euler operator `z d/dz`, because a complex derivative restricts to the
real derivative along the real axis.  Iterating needs the identification to hold on a whole
neighbourhood, which the preimage of an open set supplies.
-/

open Complex Filter

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The real trace of an open set of the plane. -/
theorem isOpen_ofReal_preimage {U : Set ℂ} (hU : IsOpen U) :
    IsOpen (((↑) : ℝ → ℂ) ⁻¹' U) :=
  hU.preimage Complex.continuous_ofReal

/-- **The real Euler jets of a complex-analytic function are its complex Euler jets.** -/
theorem eulerDeriv_iterate_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F U) :
    ∀ (k : ℕ) {x : ℝ}, ((x : ℝ) : ℂ) ∈ U →
      eulerDeriv^[k] (fun y : ℝ => F ((y : ℝ) : ℂ)) x = cEulerDeriv^[k] F ((x : ℝ) : ℂ)
  | 0, x, _ => rfl
  | (k + 1), x, hx => by
    have hVopen := isOpen_ofReal_preimage hU
    have hxV : x ∈ ((↑) : ℝ → ℂ) ⁻¹' U := hx
    have hIH : ∀ y ∈ ((↑) : ℝ → ℂ) ⁻¹' U,
        eulerDeriv^[k] (fun y : ℝ => F ((y : ℝ) : ℂ)) y = cEulerDeriv^[k] F ((y : ℝ) : ℂ) :=
      fun y hy => eulerDeriv_iterate_ofReal hU hF k hy
    have heq : eulerDeriv^[k] (fun y : ℝ => F ((y : ℝ) : ℂ))
        =ᶠ[nhds x] fun y : ℝ => cEulerDeriv^[k] F ((y : ℝ) : ℂ) :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds hxV) hIH
    have hdiff : DifferentiableAt ℂ (cEulerDeriv^[k] F) ((x : ℝ) : ℂ) :=
      (analyticOnNhd_cEulerDeriv_iterate hF k ((x : ℝ) : ℂ) hx).differentiableAt
    have hreal : HasDerivAt (fun y : ℝ => cEulerDeriv^[k] F ((y : ℝ) : ℂ))
        (deriv (cEulerDeriv^[k] F) ((x : ℝ) : ℂ)) x :=
      (hdiff.hasDerivAt).comp_ofReal
    rw [Function.iterate_succ_apply', eulerDeriv, heq.deriv_eq, hreal.deriv,
      Function.iterate_succ_apply', cEulerDeriv]

end RHTower
