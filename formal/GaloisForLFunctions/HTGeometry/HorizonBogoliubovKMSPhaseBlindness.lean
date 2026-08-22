import GaloisForLFunctions.HTGeometry.FinitePassiveResponse
import GaloisForLFunctions.HTGeometry.HorizonBogoliubovModeGaugeHolonomy

/-!
# KMS blindness to thermal-horizon Bogoliubov phase

Canonical KMS/Wightman response forms square a complex transition amplitude before constructing
the passive spectral response.  Consequently the coupled thermal-horizon phase

`exp (-i * inverseSurfaceGravity * outgoingFrequency * logIncomingFrequency)`

is invisible to every such intensity and response.  Its alternating rectangle holonomy is
nevertheless the nontrivial gauge-invariant phase

`exp (-i * inverseSurfaceGravity * ΔoutgoingFrequency * ΔlogIncomingFrequency)`.

This is an exact obstruction to obtaining phase-sensitive cross-horizon incidence from thermal
intensity or passivity alone.  The positive survivor is the rectangle holonomy: it retains the
coupled Bogoliubov datum after arbitrary separate incoming/outgoing phase calibrations.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Unit-modulus coupled phase of an ideal thermal-horizon Bogoliubov kernel. -/
def thermalHorizonCoupledPhaseKernel
    (inverseSurfaceGravity outgoingFrequency logIncomingFrequency : ℝ) : ℂ :=
  Complex.exp
    (-Complex.I * (inverseSurfaceGravity : ℂ) *
      (outgoingFrequency : ℂ) * (logIncomingFrequency : ℂ))

/-- The coupled thermal-horizon phase has unit intensity. -/
theorem normSq_thermalHorizonCoupledPhaseKernel
    (inverseSurfaceGravity outgoingFrequency logIncomingFrequency : ℝ) :
    Complex.normSq
        (thermalHorizonCoupledPhaseKernel inverseSurfaceGravity
          outgoingFrequency logIncomingFrequency) = 1 := by
  rw [Complex.normSq_eq_norm_sq, thermalHorizonCoupledPhaseKernel,
    Complex.norm_exp]
  norm_num

/-- Multiplying an amplitude by a pointwise unit phase leaves its Wightman intensity unchanged. -/
theorem wightmanTransitionIntensity_mul_of_normSq_eq_one
    {α : Type*} (weight : α → α → ℝ) (amplitude phase : α → α → ℂ)
    (hphase : ∀ a b, Complex.normSq (phase a b) = 1) (a b : α) :
    wightmanTransitionIntensity weight (fun i j => phase i j * amplitude i j) a b =
      wightmanTransitionIntensity weight amplitude a b := by
  rw [wightmanTransitionIntensity, wightmanTransitionIntensity,
    Complex.normSq_mul, hphase, one_mul]

/-- Finite KMS/Wightman transition intensity cannot observe the coupled horizon phase. -/
theorem finiteKMSWightmanTransitionIntensity_thermalHorizonPhase
    {α : Type*} [Fintype α]
    (β inverseSurfaceGravity : ℝ)
    (energy outgoingFrequency logIncomingFrequency : α → ℝ)
    (amplitude : α → α → ℂ) (a b : α) :
    finiteKMSWightmanTransitionIntensity β energy
        (fun i j =>
          thermalHorizonCoupledPhaseKernel inverseSurfaceGravity
            (outgoingFrequency i) (logIncomingFrequency j) * amplitude i j) a b =
      finiteKMSWightmanTransitionIntensity β energy amplitude a b := by
  apply wightmanTransitionIntensity_mul_of_normSq_eq_one
  intro i j
  exact normSq_thermalHorizonCoupledPhaseKernel _ _ _

/-- Every finite passive KMS response is likewise blind to the coupled horizon phase. -/
theorem finiteTransitionPassiveResponse_thermalHorizonPhase
    {α : Type*} [Fintype α]
    (β inverseSurfaceGravity : ℝ)
    (energy outgoingFrequency logIncomingFrequency : α → ℝ)
    (amplitude : α → α → ℂ) (z : ℂ) :
    finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity β energy
          (fun i j =>
            thermalHorizonCoupledPhaseKernel inverseSurfaceGravity
              (outgoingFrequency i) (logIncomingFrequency j) * amplitude i j))
        energy z =
      finiteTransitionPassiveResponse
        (finiteKMSWightmanTransitionIntensity β energy amplitude) energy z := by
  unfold finiteTransitionPassiveResponse
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [finiteKMSWightmanTransitionIntensity_thermalHorizonPhase]

/-- Rectangle holonomy retains exactly the coupled horizon phase erased by KMS intensity. -/
theorem rectangleKernelHolonomy_thermalHorizonCoupledPhaseKernel
    (inverseSurfaceGravity x₁ x₂ ℓ₁ ℓ₂ : ℝ) :
    GaloisForLFunctions.HTGeometry.rectangleKernelHolonomy
        (thermalHorizonCoupledPhaseKernel inverseSurfaceGravity)
        x₁ x₂ ℓ₁ ℓ₂ =
      Complex.exp
        (-Complex.I * (inverseSurfaceGravity : ℂ) *
          ((x₁ - x₂ : ℝ) : ℂ) * ((ℓ₁ - ℓ₂ : ℝ) : ℂ)) := by
  change GaloisForLFunctions.HTGeometry.rectangleKernelHolonomy
      (GaloisForLFunctions.HTGeometry.exponentialKernel
        (fun x ℓ : ℝ =>
          -Complex.I * (inverseSurfaceGravity : ℂ) * (x : ℂ) * (ℓ : ℂ)))
      x₁ x₂ ℓ₁ ℓ₂ = _
  rw [GaloisForLFunctions.HTGeometry.rectangleKernelHolonomy_exponentialKernel]
  congr 1
  simp only [GaloisForLFunctions.HTGeometry.rectanglePhaseDefect]
  push_cast
  ring

end

end HTGeometry
