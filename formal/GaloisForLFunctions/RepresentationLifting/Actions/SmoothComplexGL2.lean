import GaloisForLFunctions.RepresentationLifting.Actions.SmoothConnectedActions
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Triviality of smooth complex GL₂ actions

Connected root groups force determinant descent. Complex scalar matrices
lie on exponential paths from the identity and therefore act trivially.
Every nonzero complex number is a square, so scalar triviality kills the
remaining determinant action. No dimension or characteristic restriction
is imposed on the coefficient module.
Smoothness means that each vector is fixed on some identity neighborhood.
-/

noncomputable section
open Filter Topology Matrix
namespace GaloisForLFunctions.RepresentationLifting.ComplexGL2

private def expUnit (z : ℂ) : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

private theorem continuous_expUnit : Continuous expUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · exact Complex.continuous_exp
  · change Continuous (fun z : ℂ => (Complex.exp z)⁻¹)
    exact Complex.continuous_exp.inv₀ Complex.exp_ne_zero

private theorem continuous_scalar :
    Continuous (GeneralLinearGroup.scalar (Fin 2) : ℂˣ → GeneralLinearGroup (Fin 2) ℂ) := by
  simp_rw [Units.continuous_iff, ← map_inv, GeneralLinearGroup.coe_scalar]
  constructor
  · apply continuous_matrix
    intro i j
    change Continuous (fun u : ℂˣ => if i = j then (u : ℂ) else 0)
    split_ifs <;> fun_prop
  · apply continuous_matrix
    intro i j
    change Continuous (fun u : ℂˣ => if i = j then ((u⁻¹ : ℂˣ) : ℂ) else 0)
    split_ifs <;> fun_prop

private theorem unit_square (u : ℂˣ) : ∃ v : ℂˣ, v ^ 2 = u := by
  refine ⟨expUnit (Complex.log (u : ℂ) / 2), Units.ext ?_⟩
  change Complex.exp (Complex.log (u : ℂ) / 2) ^ 2 = (u : ℂ)
  rw [pow_two, ← Complex.exp_add,
    show Complex.log (u : ℂ) / 2 + Complex.log (u : ℂ) / 2 = Complex.log (u : ℂ) by ring,
    Complex.exp_log u.ne_zero]

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Every smooth complex GL₂ action kills scalar matrices, without a dimension restriction. -/
theorem smooth_scalar_trivial
    (ρ : GeneralLinearGroup (Fin 2) ℂ →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℂ), ρ g v = v)
    (u : ℂˣ) : ρ (GeneralLinearGroup.scalar (Fin 2) u) = 1 := by
  have h0 : GeneralLinearGroup.scalar (Fin 2) (expUnit 0) = 1 := by
    have he : expUnit 0 = 1 := by ext; exact Complex.exp_zero
    rw [he, map_one]
  have h := ConnectedActions.connected_family_trivial ρ hρ
    (fun z : ℂ => GeneralLinearGroup.scalar (Fin 2) (expUnit z))
    (continuous_scalar.comp continuous_expUnit) 0 h0 (Complex.log (u : ℂ))
  have hu : expUnit (Complex.log (u : ℂ)) = u := Units.ext (Complex.exp_log u.ne_zero)
  simpa only [hu] using h

/-- Every smooth representation of GL₂(ℂ) on an arbitrary coefficient module is trivial. -/
theorem smooth_action_trivial
    (ρ : GeneralLinearGroup (Fin 2) ℂ →* (V ≃ₗ[k] V))
    (hρ : ∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℂ), ρ g v = v)
    (g : GeneralLinearGroup (Fin 2) ℂ) : ρ g = 1 := by
  obtain ⟨χ, hχ, _⟩ := ConnectedActions.smooth_det_factor ρ hρ
  obtain ⟨u, hu⟩ := unit_square (GeneralLinearGroup.det g)
  have hs := smooth_scalar_trivial ρ hρ u
  rw [← hχ] at hs ⊢
  change χ (GeneralLinearGroup.det g) = 1
  change χ (GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) u)) = 1 at hs
  rw [GeneralLinearGroup.det_scalar] at hs
  simp only [Fintype.card_fin, hu] at hs
  exact hs

/-- Smoothness for a complex GL₂ action is exactly pointwise triviality. -/
theorem smooth_iff_trivial (ρ : GeneralLinearGroup (Fin 2) ℂ →* (V ≃ₗ[k] V)) :
    (∀ v : V, ∀ᶠ g in 𝓝 (1 : GeneralLinearGroup (Fin 2) ℂ), ρ g v = v) ↔
      ∀ g, ρ g = 1 := by
  constructor
  · exact smooth_action_trivial ρ
  · intro h v
    exact Filter.Eventually.of_forall (fun g => by rw [h g]; rfl)

#print axioms smooth_scalar_trivial
#print axioms smooth_action_trivial
#print axioms smooth_iff_trivial
end GaloisForLFunctions.RepresentationLifting.ComplexGL2
