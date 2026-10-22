import GaloisForLFunctions.RHTower.Suzuki.SuzukiGlobalPhaseConjugacy

/-!
# Differentiability of the global phase transport

The transport between two global phases is `φₛ⁻¹ ∘ φᵣ`, so its derivative is not an extra
assumption: wherever the source phase has nonzero speed and the reference phase is differentiable,
the transport is differentiable with speed the ratio of the two phase speeds.  The inverse
function theorem for a continuous order isomorphism supplies the inverse branch.

Consequently the Jacobian layer of the conjugacy — phase speed, Clark atom mass, Donoghue
probability mass — needs only the two phase derivatives, and the layer is non-vacuous: increasing
affine maps realize every pair of positive phase speeds.
-/

open Filter

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Transport Jacobian.**  The global phase transport is differentiable wherever the source
phase has nonzero speed at the transported point and the reference phase is differentiable, and
its speed is the ratio of the two phase speeds. -/
theorem hasDerivAt_suzukiPhaseTransport
    {φₛ φᵣ : ℝ ≃o ℝ} {x phaseSpeedₛ phaseSpeedᵣ : ℝ}
    (hphaseₛ : HasDerivAt φₛ phaseSpeedₛ (suzukiPhaseTransport φₛ φᵣ x))
    (hphaseᵣ : HasDerivAt φᵣ phaseSpeedᵣ x)
    (hphaseSpeedₛ : phaseSpeedₛ ≠ 0) :
    HasDerivAt (suzukiPhaseTransport φₛ φᵣ) (phaseSpeedₛ⁻¹ * phaseSpeedᵣ) x := by
  rw [suzukiPhaseTransport_apply] at hphaseₛ
  have hinv : HasDerivAt (φₛ.symm : ℝ → ℝ) phaseSpeedₛ⁻¹ (φᵣ x) :=
    hphaseₛ.of_local_left_inverse φₛ.symm.continuous.continuousAt hphaseSpeedₛ
      (Filter.Eventually.of_forall fun z => φₛ.apply_symm_apply z)
  have hcomp := hinv.comp x hphaseᵣ
  have hfun : ((φₛ.symm : ℝ → ℝ) ∘ (φᵣ : ℝ → ℝ)) =
      (suzukiPhaseTransport φₛ φᵣ : ℝ → ℝ) := by
    funext y
    simp [Function.comp_apply, suzukiPhaseTransport_apply]
  rwa [hfun] at hcomp

/-- The phase-speed transport law with its derivative hypothesis discharged. -/
theorem suzukiPhaseTransport_phaseSpeed_of_phases
    {φₛ φᵣ : ℝ ≃o ℝ} {x phaseSpeedₛ phaseSpeedᵣ : ℝ}
    (hphaseₛ : HasDerivAt φₛ phaseSpeedₛ (suzukiPhaseTransport φₛ φᵣ x))
    (hphaseᵣ : HasDerivAt φᵣ phaseSpeedᵣ x)
    (hphaseSpeedₛ : phaseSpeedₛ ≠ 0) :
    phaseSpeedₛ * (phaseSpeedₛ⁻¹ * phaseSpeedᵣ) = phaseSpeedᵣ :=
  suzukiPhaseTransport_phaseSpeed
    (hasDerivAt_suzukiPhaseTransport hphaseₛ hphaseᵣ hphaseSpeedₛ) hphaseₛ hphaseᵣ

/-- The Clark atom Jacobian with its transport hypothesis discharged: the transported atom mass
is the old one scaled by the ratio of phase speeds. -/
theorem suzukiPhaseTransport_atomMass_of_phases
    {φₛ φᵣ : ℝ ≃o ℝ} {x phaseSpeedₛ phaseSpeedᵣ atomMassₛ atomMassᵣ : ℝ}
    (hphaseₛ : HasDerivAt φₛ phaseSpeedₛ (suzukiPhaseTransport φₛ φᵣ x))
    (hphaseᵣ : HasDerivAt φᵣ phaseSpeedᵣ x)
    (hphaseSpeedₛ : phaseSpeedₛ ≠ 0) (hphaseSpeedᵣ : phaseSpeedᵣ ≠ 0)
    (hatomMassₛ : atomMassₛ = 2 / phaseSpeedₛ)
    (hatomMassᵣ : atomMassᵣ = 2 / phaseSpeedᵣ) :
    atomMassₛ = phaseSpeedₛ⁻¹ * phaseSpeedᵣ * atomMassᵣ :=
  suzukiPhaseTransport_atomMass
    (hasDerivAt_suzukiPhaseTransport hphaseₛ hphaseᵣ hphaseSpeedₛ)
    hphaseₛ hphaseᵣ hphaseSpeedₛ hphaseSpeedᵣ hatomMassₛ hatomMassᵣ

/-! ## The layer is non-vacuous -/

/-- An increasing affine bijection of the line, as an order isomorphism. -/
def affineOrderIso {a : ℝ} (ha : 0 < a) (b : ℝ) : ℝ ≃o ℝ where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    field_simp
    ring
  right_inv y := by
    field_simp
    ring
  map_rel_iff' := by
    intro x y
    show a * x + b ≤ a * y + b ↔ x ≤ y
    constructor
    · intro h
      nlinarith
    · intro h
      nlinarith

@[simp] theorem affineOrderIso_apply {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    affineOrderIso ha b x = a * x + b := rfl

/-- An increasing affine phase has constant speed equal to its slope. -/
theorem hasDerivAt_affineOrderIso {a : ℝ} (ha : 0 < a) (b x : ℝ) :
    HasDerivAt (affineOrderIso ha b) a x := by
  have h : HasDerivAt (fun y : ℝ => a * y + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  exact h

/-- Affine phases realize the transport Jacobian at every pair of positive speeds, so the
differentiable-transport layer is inhabited and its transport speed takes every positive value. -/
theorem hasDerivAt_suzukiPhaseTransport_affine
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (b₁ b₂ x : ℝ) :
    HasDerivAt (suzukiPhaseTransport (affineOrderIso ha₁ b₁) (affineOrderIso ha₂ b₂))
      (a₁⁻¹ * a₂) x :=
  hasDerivAt_suzukiPhaseTransport
    (hasDerivAt_affineOrderIso ha₁ b₁ _) (hasDerivAt_affineOrderIso ha₂ b₂ x) ha₁.ne'

end

end GaloisForLFunctions.RHTower
