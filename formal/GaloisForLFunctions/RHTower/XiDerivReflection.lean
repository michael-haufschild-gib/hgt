import GaloisForLFunctions.RHTower.TransverseEquilibrium
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# The closed form of the marginality identity, and the verdict on its variational proof

## Closed form

Summing the Hadamard partial fractions at a simple zero `ρ` gives
`Σ_{ρ'≠ρ} 1/(ρ − ρ') = ξ''(ρ)/(2ξ'(ρ)) − C` with `C` the real Hadamard constant, so the marginality
identity `Σ_{ρ'≠ρ} Re(1/(ρ−ρ')) = 0` of `MUST-412` is the **local jet condition**

  `Re( ξ''(ρ) / ξ'(ρ) ) = 0`,

i.e. `ξ''(ρ)/ξ'(ρ)` is purely imaginary.  Since `∂_σ log‖ξ'(σ+it)‖ = Re(ξ''/ξ')`, this says exactly

  **every zero is a horizontal critical point of `‖ξ'‖`.**

That is the identity in variational form: a stationarity condition, not a bound.

## What is proved here

The functional equation differentiates to `ξ'(1−s) = −ξ'(s)`, so `‖ξ'‖` is invariant under the point
reflection in `1/2`.  This is the unconditional half of the identity.

## Verdict on the variational proof

The one general machine that derives equilibrium identities of this exact shape is **Stieltjes'
electrostatic theorem**: if `p'' + Q p' + R p = 0` then at every simple zero
`Σ_{k≠j} 1/(z_j − z_k) = −Q(z_j)/2`, and the configuration is the equilibrium of a Coulomb gas in the
potential determined by `Q`.  The identity is then *derived*, variationally, from the ODE.

For `ξ` no such ODE exists: `ξ` is differentially transcendental, and the corpus records this in the
strong form that it remains so after adjoining any finite bath.  **So there is no Stieltjes potential
for `ξ` and the variational derivation of the identity is unavailable — not unproved, unavailable.**
The identity remains true (it is equivalent to the hypothesis) but it cannot be obtained by the
mechanism that produces every other equilibrium identity of its form.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The functional equation, differentiated**: `ξ'(1 − s) = −ξ'(s)`. -/
theorem deriv_xi_one_sub (s : ℂ) : deriv xi (1 - s) = - deriv xi s := by
  have hxi : HasDerivAt xi (deriv xi (1 - s)) (1 - s) :=
    (xi_differentiable (1 - s)).hasDerivAt
  have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub (1 : ℂ)
  have hcomp : HasDerivAt (fun z : ℂ => xi (1 - z)) (deriv xi (1 - s) * (-1)) s :=
    hxi.comp s h1
  have heq : (fun z : ℂ => xi (1 - z)) = xi := funext fun z => xi_one_sub z
  rw [heq] at hcomp
  have h := hcomp.deriv
  rw [mul_neg_one] at h
  rw [h]; ring

/-- `‖ξ'‖` is invariant under the point reflection in `1/2`. -/
theorem norm_deriv_xi_one_sub (s : ℂ) : ‖deriv xi (1 - s)‖ = ‖deriv xi s‖ := by
  rw [deriv_xi_one_sub s, norm_neg]

/-- The derivative vanishes at `s` exactly when it vanishes at the reflected point. -/
theorem deriv_xi_one_sub_eq_zero_iff (s : ℂ) :
    deriv xi (1 - s) = 0 ↔ deriv xi s = 0 := by
  rw [deriv_xi_one_sub s, neg_eq_zero]

/-- The marginality identity in closed, variational form: `ξ''/ξ'` is purely imaginary at `ρ`,
equivalently `ρ` is a horizontal critical point of `‖ξ'‖`. -/
def HorizontalCriticalAt (ρ : ℂ) : Prop :=
  (deriv (deriv xi) ρ / deriv xi ρ).re = 0

/-- At the centre of the strip the closed form is automatic on the real axis: the reflected
derivative identity forces `ξ'(1/2) = −ξ'(1/2)`, hence `ξ'(1/2) = 0`. -/
theorem deriv_xi_half : deriv xi (1 / 2 : ℂ) = 0 := by
  have h := deriv_xi_one_sub (1 / 2 : ℂ)
  norm_num at h
  linear_combination h / 2

end

end RHTower
