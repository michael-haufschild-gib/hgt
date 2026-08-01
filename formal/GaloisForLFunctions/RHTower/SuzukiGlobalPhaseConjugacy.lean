import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import GaloisForLFunctions.RHTower.SuzukiFiniteShiftProjectiveHolonomy

/-!
# Suzuki's global phase-conjugacy divisor flow

At fixed aperture, the normalized Suzuki boundary phase is strictly increasing and proper on
paper: its Donoghue measure is pure point and cyclic on an infinite-dimensional space, while
parity makes its support two-sided.  Thus the phase is an order isomorphism `ℝ ≃o ℝ`.

This module formalizes the dependency-closed consequence.  If `φᵣ` and `φₛ` are the global phase
charts at two admissible shifts, then

`T_(s←r) = φₛ⁻¹ ∘ φᵣ`

is an exact flat transport for every lifted spectral level.  Differentiating the phase identity
transports the whole phase-speed density.  Since Suzuki's Clark/Nevanlinna atom mass is `2 / φ'`,
the atom mass transforms by the Jacobian of `T_(s←r)`.  The normalized spectral probability and
the restricted-Weil source weight follow from the same identity.

The final theorem connects a globally fixed phase level to the logarithmic source generator from
`SuzukiFiniteShiftProjectiveHolonomy`.  No RH assumption and no numerical computation occur.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Global phase charts and their flat transport -/

/-- Exact real-line transport from the global phase chart `φᵣ` to `φₛ`. -/
def suzukiPhaseTransport (φₛ φᵣ : ℝ ≃o ℝ) : ℝ ≃o ℝ :=
  φᵣ.trans φₛ.symm

/-- Spectral point at one fixed lifted phase level.  Taking the level to be
`θ + π + 2πk` gives Suzuki's angle-`θ`, label-`k` extension eigenvalue. -/
def suzukiPhasePole (φ : ℝ ≃o ℝ) (level : ℝ) : ℝ :=
  φ.symm level

@[simp] theorem suzukiPhaseTransport_apply (φₛ φᵣ : ℝ ≃o ℝ) (x : ℝ) :
    suzukiPhaseTransport φₛ φᵣ x = φₛ.symm (φᵣ x) :=
  rfl

/-- Transport preserves the complete lifted phase, not merely its value modulo `2π`. -/
@[simp] theorem suzukiPhaseTransport_phase (φₛ φᵣ : ℝ ≃o ℝ) (x : ℝ) :
    φₛ (suzukiPhaseTransport φₛ φᵣ x) = φᵣ x := by
  simp [suzukiPhaseTransport]

/-- Transport from a global phase chart to itself is the identity. -/
@[simp] theorem suzukiPhaseTransport_self (φ : ℝ ≃o ℝ) :
    suzukiPhaseTransport φ φ = OrderIso.refl ℝ := by
  ext x
  simp [suzukiPhaseTransport]

/-- **Flat phase cocycle.** Every intermediate global phase chart cancels exactly. -/
theorem suzukiPhaseTransport_comp (φₜ φₛ φᵣ : ℝ ≃o ℝ) :
    (suzukiPhaseTransport φₛ φᵣ).trans (suzukiPhaseTransport φₜ φₛ) =
      suzukiPhaseTransport φₜ φᵣ := by
  ext x
  simp [suzukiPhaseTransport]

/-- Reversing the endpoints reverses the global phase transport. -/
@[simp] theorem suzukiPhaseTransport_symm (φₛ φᵣ : ℝ ≃o ℝ) :
    (suzukiPhaseTransport φₛ φᵣ).symm = suzukiPhaseTransport φᵣ φₛ := by
  ext x
  simp [suzukiPhaseTransport]

/-- A fixed lifted spectral level is transported to the same level at the new shift. -/
theorem suzukiPhaseTransport_level
    (φₛ φᵣ : ℝ ≃o ℝ) {x level : ℝ} (hx : φᵣ x = level) :
    φₛ (suzukiPhaseTransport φₛ φᵣ x) = level := by
  rw [suzukiPhaseTransport_phase, hx]

/-- Consequently every globally phase-labeled Suzuki pole is transported exactly. -/
@[simp] theorem suzukiPhaseTransport_pole (φₛ φᵣ : ℝ ≃o ℝ) (level : ℝ) :
    suzukiPhaseTransport φₛ φᵣ (suzukiPhasePole φᵣ level) =
      suzukiPhasePole φₛ level := by
  simp [suzukiPhaseTransport, suzukiPhasePole]

/-- Distinct lifted phase labels remain strictly ordered, so labeled poles cannot collide. -/
theorem suzukiPhasePole_lt_phasePole
    (φ : ℝ ≃o ℝ) {level₁ level₂ : ℝ} (hlevel : level₁ < level₂) :
    suzukiPhasePole φ level₁ < suzukiPhasePole φ level₂ :=
  φ.symm.strictMono hlevel

/-- Global phase transport is orientation preserving. -/
theorem suzukiPhaseTransport_strictMono (φₛ φᵣ : ℝ ≃o ℝ) :
    StrictMono (suzukiPhaseTransport φₛ φᵣ) :=
  (suzukiPhaseTransport φₛ φᵣ).strictMono

/-! ## Phase-cell mass -/

/-- **Invariant phase-cell mass.**  The phase-speed density integrates over the cell between two
lifted phase levels to exactly the phase increment: the density is the derivative of the chart, so
the fundamental theorem of calculus telescopes the cell to its labels. -/
theorem integral_phaseSpeed_phaseCell
    {φ : ℝ ≃o ℝ} {q : ℝ → ℝ} (level cell : ℝ)
    (hderiv : ∀ x ∈ Set.uIcc (suzukiPhasePole φ level) (suzukiPhasePole φ (level + cell)),
      HasDerivAt (⇑φ) (q x) x)
    (hint : IntervalIntegrable q MeasureTheory.volume
      (suzukiPhasePole φ level) (suzukiPhasePole φ (level + cell))) :
    (∫ x in (suzukiPhasePole φ level)..(suzukiPhasePole φ (level + cell)), q x) = cell := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [suzukiPhasePole, OrderIso.apply_symm_apply]
  ring

/-- The full-turn cell carries mass `2 π`, which is the normalization of Suzuki's angle labels. -/
theorem integral_phaseSpeed_fullTurn
    {φ : ℝ ≃o ℝ} {q : ℝ → ℝ} (level : ℝ)
    (hderiv : ∀ x ∈ Set.uIcc (suzukiPhasePole φ level)
        (suzukiPhasePole φ (level + 2 * Real.pi)),
      HasDerivAt (⇑φ) (q x) x)
    (hint : IntervalIntegrable q MeasureTheory.volume
      (suzukiPhasePole φ level) (suzukiPhasePole φ (level + 2 * Real.pi))) :
    (∫ x in (suzukiPhasePole φ level)..(suzukiPhasePole φ (level + 2 * Real.pi)), q x)
      = 2 * Real.pi :=
  integral_phaseSpeed_phaseCell level (2 * Real.pi) hderiv hint

/-! ## Phase-speed and atom-weight Jacobians -/

/-- Differentiating `φₛ(T(x)) = φᵣ(x)` transports the complete phase-speed density. -/
theorem suzukiPhaseTransport_phaseSpeed
    {φₛ φᵣ : ℝ ≃o ℝ} {x transportSpeed phaseSpeedₛ phaseSpeedᵣ : ℝ}
    (htransport : HasDerivAt (suzukiPhaseTransport φₛ φᵣ) transportSpeed x)
    (hphaseₛ : HasDerivAt φₛ phaseSpeedₛ (suzukiPhaseTransport φₛ φᵣ x))
    (hphaseᵣ : HasDerivAt φᵣ phaseSpeedᵣ x) :
    phaseSpeedₛ * transportSpeed = phaseSpeedᵣ := by
  have hcomp : HasDerivAt
      (fun y => φₛ (suzukiPhaseTransport φₛ φᵣ y))
      (phaseSpeedₛ * transportSpeed) x :=
    hphaseₛ.comp x htransport
  have hphaseᵣ' : HasDerivAt
      (fun y => φₛ (suzukiPhaseTransport φₛ φᵣ y)) phaseSpeedᵣ x :=
    hphaseᵣ.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (suzukiPhaseTransport_phase φₛ φᵣ))
  exact hcomp.unique hphaseᵣ'

/-- **Clark atom Jacobian.** If atom mass is reciprocal phase speed, global phase transport
multiplies the old mass by the transport derivative. -/
theorem suzukiPhaseTransport_atomMass
    {φₛ φᵣ : ℝ ≃o ℝ}
    {x transportSpeed phaseSpeedₛ phaseSpeedᵣ atomMassₛ atomMassᵣ : ℝ}
    (htransport : HasDerivAt (suzukiPhaseTransport φₛ φᵣ) transportSpeed x)
    (hphaseₛ : HasDerivAt φₛ phaseSpeedₛ (suzukiPhaseTransport φₛ φᵣ x))
    (hphaseᵣ : HasDerivAt φᵣ phaseSpeedᵣ x)
    (hphaseSpeedₛ : phaseSpeedₛ ≠ 0) (hphaseSpeedᵣ : phaseSpeedᵣ ≠ 0)
    (hatomMassₛ : atomMassₛ = 2 / phaseSpeedₛ)
    (hatomMassᵣ : atomMassᵣ = 2 / phaseSpeedᵣ) :
    atomMassₛ = transportSpeed * atomMassᵣ := by
  have hspeed := suzukiPhaseTransport_phaseSpeed htransport hphaseₛ hphaseᵣ
  rw [hatomMassₛ, hatomMassᵣ]
  field_simp [hphaseSpeedₛ, hphaseSpeedᵣ]
  linarith

/-- The normalized Donoghue spectral probability inherits the atom Jacobian with the exact
compactifying factors `(1+x²)/(1+T(x)²)`. -/
theorem suzukiPhaseTransport_probabilityMass
    {x y transportSpeed atomMassₛ atomMassᵣ probabilityMassₛ probabilityMassᵣ : ℝ}
    (hatom : atomMassₛ = transportSpeed * atomMassᵣ)
    (hprobabilityₛ : probabilityMassₛ = atomMassₛ / (1 + y ^ 2))
    (hprobabilityᵣ : probabilityMassᵣ = atomMassᵣ / (1 + x ^ 2)) :
    probabilityMassₛ =
      transportSpeed * (1 + x ^ 2) / (1 + y ^ 2) * probabilityMassᵣ := by
  have hx : 1 + x ^ 2 ≠ 0 := by positivity
  have hy : 1 + y ^ 2 ≠ 0 := by positivity
  rw [hprobabilityₛ, hprobabilityᵣ, hatom]
  field_simp [hx, hy]

/-- Substituting Suzuki's restricted-Weil source formula on both sides of the atom Jacobian gives
the exact Fourier-amplitude/eigenvector-norm transport law. -/
theorem suzukiPhaseTransport_sourceNormWeight
    {transportSpeed atomMassₛ atomMassᵣ sourceNormWeightₛ sourceNormWeightᵣ : ℝ}
    (hatom : atomMassₛ = transportSpeed * atomMassᵣ)
    (hsourceₛ : atomMassₛ = sourceNormWeightₛ)
    (hsourceᵣ : atomMassᵣ = sourceNormWeightᵣ) :
    sourceNormWeightₛ = transportSpeed * sourceNormWeightᵣ := by
  rw [← hsourceₛ, ← hsourceᵣ, hatom]

/-! ## Global fixed-level velocity and the finite-shift source generator -/

/-- A globally fixed phase level has the same exact velocity as the local Clark calculation.
The hypothesis `q * x' = i Ξ` is the derivative of
`φ_r(x(r)) = constant` after using `∂ᵣ φ_r = -i Ξ`. -/
theorem suzukiGlobalPoleVelocity_eq_sourceGenerator
    {Ξ : ℂ} {phaseSpeed atomMass poleVelocity : ℝ}
    (hphaseSpeed : phaseSpeed ≠ 0)
    (hatomMass : atomMass = 2 / phaseSpeed)
    (hlevel : (phaseSpeed : ℂ) * (poleVelocity : ℂ) = I * Ξ) :
    (poleVelocity : ℂ) = I * (atomMass : ℂ) * Ξ / 2 := by
  calc
    (poleVelocity : ℂ) = -Ξ / (I * (phaseSpeed : ℂ)) := by
      field_simp [hphaseSpeed]
      calc
        (poleVelocity : ℂ) * I * (phaseSpeed : ℂ) =
            I * ((phaseSpeed : ℂ) * (poleVelocity : ℂ)) := by ring
        _ = I * (I * Ξ) := by rw [hlevel]
        _ = -Ξ := by rw [← mul_assoc, I_mul_I]; ring
    _ = I * (atomMass : ℂ) * Ξ / 2 :=
      suzukiImplicitPoleVelocity_eq_clarkTransport hphaseSpeed hatomMass

end GaloisForLFunctions.RHTower
