import GaloisForLFunctions.HTGeometry.AppellHumbertGaussianBound
import GaloisForLFunctions.HTGeometry.QuasiAbelianPoincareSeries

/-!
# The Appell--Humbert factor as an automorphic factor

The damping chain of the quasi-abelian jet-ampleness induction is stated for an
`AutomorphicFactor`, and the Gaussian decay it needs is the positivity of a Hermitian form.  This
module produces the factor: for a Hermitian form on `ℂ^d` and a semicharacter of unit modulus the
Appell--Humbert expression is normalised, satisfies the cocycle law, is nowhere zero and is entire
on every line, so it is an `AutomorphicFactor` for any period group.

Entireness is free: the form is complex-linear in the first argument, so restricted to a line the
exponent is affine.  Continuity is free for the same reason, since `ℂ^d` is finite dimensional.

* `IsHermitianForm.hermLeft`, `IsHermitianForm.zero_right`, `semicharacter_zero`;
* `appellHumbertAutomorphicFactor` — **the factor**;
* `norm_inv_appellHumbertAutomorphicFactor_le` — **its Gaussian bound**, in the form the damping
  estimate consumes.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

namespace IsHermitianForm

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : V → V → ℂ} (hH : IsHermitianForm H)

include hH

theorem zero_left (y : V) : H 0 y = 0 := by
  have h := hH.add_left 0 0 y
  rw [add_zero] at h
  linear_combination -h

theorem zero_right (x : V) : H x 0 = 0 := by
  rw [hH.symm 0 x, hH.zero_left x, star_zero]

/-- The form is complex-linear in its first argument. -/
def hermLeft (γ : V) : V →ₗ[ℂ] ℂ where
  toFun := fun x => H x γ
  map_add' := fun x y => hH.add_left x y γ
  map_smul' := fun a x => by
    simpa using hH.smul_left a x γ

@[simp] theorem hermLeft_apply (γ x : V) : hH.hermLeft γ x = H x γ := rfl

end IsHermitianForm

section Factor

variable {d : ℕ} {H : (Fin d → ℂ) → (Fin d → ℂ) → ℂ} (hH : IsHermitianForm H)
variable {χ : (Fin d → ℂ) → ℂ}

include hH

/-- A unit-modulus semicharacter takes the value one at zero. -/
theorem semicharacter_zero (hχ : ∀ γ, ‖χ γ‖ = 1)
    (hsemi : ∀ γ γ' : Fin d → ℂ, χ (γ + γ')
      = χ γ * χ γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H γ γ').im : ℝ)))) :
    χ 0 = 1 := by
  have h := hsemi 0 0
  rw [add_zero, hH.zero_left 0] at h
  simp only [Complex.zero_im, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    mul_one] at h
  have hne : χ 0 ≠ 0 := by
    intro h0
    have := hχ 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  field_simp at h
  exact h.symm

/-- The Appell--Humbert expression is continuous. -/
theorem continuous_appellHumbertFactor (γ : Fin d → ℂ) :
    Continuous fun x : Fin d → ℂ => appellHumbertFactor H χ γ x := by
  refine continuous_const.mul (Complex.continuous_exp.comp ?_)
  exact (continuous_const.mul (hH.hermLeft γ).continuous_of_finiteDimensional).add
    continuous_const

/-- The Appell--Humbert expression is entire on every line. -/
theorem lineEntire_appellHumbertFactor (γ : Fin d → ℂ) :
    LineEntire (⟨fun x : Fin d → ℂ => appellHumbertFactor H χ γ x,
      continuous_appellHumbertFactor hH γ⟩ : C(Fin d → ℂ, ℂ)) := by
  intro x w
  have hfun : (fun z : ℂ => appellHumbertFactor H χ γ (x + z • w))
      = fun z : ℂ => χ γ * Complex.exp
          ((Real.pi : ℂ) * (H x γ + z * H w γ) + ((Real.pi : ℂ) / 2) * H γ γ) := by
    funext z
    rw [appellHumbertFactor, hH.add_left x (z • w) γ, hH.smul_left z w γ]
  show Differentiable ℂ fun z : ℂ => appellHumbertFactor H χ γ (x + z • w)
  rw [hfun]
  exact Differentiable.const_mul (Differentiable.cexp (by fun_prop)) _

/-- **The Appell--Humbert factor of a Hermitian form and a unit-modulus semicharacter is an
automorphic factor for every period group.** -/
noncomputable def appellHumbertAutomorphicFactor (hχ : ∀ γ, ‖χ γ‖ = 1)
    (hsemi : ∀ γ γ' : Fin d → ℂ, χ (γ + γ')
      = χ γ * χ γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H γ γ').im : ℝ))))
    (Γ : AddSubgroup (Fin d → ℂ)) : AutomorphicFactor d Γ where
  factor := fun γ => ⟨⟨fun x => appellHumbertFactor H χ γ.1 x,
    continuous_appellHumbertFactor hH γ.1⟩, lineEntire_appellHumbertFactor hH γ.1⟩
  normalized := by
    intro x
    show appellHumbertFactor H χ ((0 : Γ) : Fin d → ℂ) x = 1
    rw [show ((0 : Γ) : Fin d → ℂ) = 0 from rfl, appellHumbertFactor, hH.zero_right x,
      hH.zero_left 0, semicharacter_zero hH hχ hsemi]
    simp
  cocycle := by
    intro γ δ x
    show appellHumbertFactor H χ ((γ + δ : Γ) : Fin d → ℂ) x
      = appellHumbertFactor H χ (γ : Fin d → ℂ) (x + δ.1)
        * appellHumbertFactor H χ (δ : Fin d → ℂ) x
    rw [show ((γ + δ : Γ) : Fin d → ℂ) = (γ : Fin d → ℂ) + (δ : Fin d → ℂ) from rfl]
    exact appellHumbertFactor_isMulTwoCocycle hH hsemi _ _ _
  nowhereZero := by
    intro γ x
    show appellHumbertFactor H χ (γ : Fin d → ℂ) x ≠ 0
    rw [appellHumbertFactor]
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    intro h0
    have := hχ (γ : Fin d → ℂ)
    rw [h0, norm_zero] at this
    exact zero_ne_one this

/-- **The Gaussian bound in the form the damping estimate consumes.** -/
theorem norm_inv_appellHumbertAutomorphicFactor_le (hpos : ∀ w : Fin d → ℂ, 0 ≤ (H w w).re)
    (hχ : ∀ γ, ‖χ γ‖ = 1)
    (hsemi : ∀ γ γ' : Fin d → ℂ, χ (γ + γ')
      = χ γ * χ γ' * Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H γ γ').im : ℝ))))
    (Γ : AddSubgroup (Fin d → ℂ)) {C : ℝ} (hC : 0 ≤ C) {x : Fin d → ℂ}
    (hx : (H x x).re ≤ C ^ 2) (γ : Γ) :
    ‖(((appellHumbertAutomorphicFactor hH hχ hsemi Γ).factor γ).1 x)⁻¹‖
      ≤ Real.exp (Real.pi * C ^ 2) * Real.exp (-(Real.pi / 4) * (H γ.1 γ.1).re) :=
  norm_inv_appellHumbertFactor_le hH hpos hχ hC hx _

end Factor

end GaloisForLFunctions.HTGeometry
