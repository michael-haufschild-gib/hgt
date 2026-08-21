import GaloisForLFunctions.HTGeometry.SeibergWitten.Connections

/-!
# Coupled Seiberg--Witten equations and gauge flow

This is the global-sections layer.  A value of `SeibergWittenData` supplies a connection carrier,
positive and negative spinor section spaces, two-form space, curvature, Dirac operator, quadratic
map, Hodge star, and the exact `U(1)` covariance laws.  They are fields of supplied geometric data,
not axioms.  A `SeibergWittenSolution` is a closed subtype satisfying both coupled equations.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Global section-space data for the coupled Abelian Seiberg--Witten equations. -/
structure SeibergWittenData
    (Connection PositiveSpinor NegativeSpinor TwoForms : Type*)
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms] where
  hodgeStar : HodgeStar TwoForms
  curvature : Connection → TwoForms
  dirac : Connection → PositiveSpinor →ₗ[ℂ] NegativeSpinor
  quadraticMap : PositiveSpinor → TwoForms
  quadraticMap_selfDual : ∀ ψ, hodgeStar.toLinearMap (quadraticMap ψ) = quadraticMap ψ
  gaugeConnection : Circle → Connection → Connection
  curvatureGaugeInvariant : ∀ u A,
    hodgeStar.selfDualPart (curvature (gaugeConnection u A)) =
      hodgeStar.selfDualPart (curvature A)
  diracGaugeCovariant : ∀ u A ψ,
    dirac (gaugeConnection u A) ((u : ℂ) • ψ) = (u : ℂ) • dirac A ψ
  quadraticMap_gaugeInvariant : ∀ (u : Circle) ψ,
    quadraticMap ((u : ℂ) • ψ) = quadraticMap ψ

/-- A configuration satisfying both the Dirac and self-dual curvature equations. -/
def SeibergWittenSolution
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms) : Type _ :=
  {configuration : Connection × PositiveSpinor //
    data.dirac configuration.1 configuration.2 = 0 ∧
      data.hodgeStar.selfDualPart (data.curvature configuration.1) =
        data.quadraticMap configuration.2}

/-- Gauge action sends every exact Seiberg--Witten solution to another exact solution. -/
def gaugeTransformSolution
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms)
    (u : Circle) : SeibergWittenSolution data → SeibergWittenSolution data :=
  fun solution => ⟨(data.gaugeConnection u solution.1.1, (u : ℂ) • solution.1.2), by
    constructor
    · rw [data.diracGaugeCovariant, solution.2.1, smul_zero]
    · rw [data.curvatureGaugeInvariant, data.quadraticMap_gaugeInvariant]
      exact solution.2.2⟩

/-- Self-dual curvature representative of a Seiberg--Witten solution. -/
def seibergWittenSolutionInvariant
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms)
    (solution : SeibergWittenSolution data) : TwoForms :=
  data.hodgeStar.selfDualPart (data.curvature solution.1.1)

/-- Gauge transformations preserve the self-dual curvature representative of every solution. -/
theorem gaugeTransformSolution_invariant
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms)
    (u : Circle) (solution : SeibergWittenSolution data) :
    seibergWittenSolutionInvariant data (gaugeTransformSolution data u solution) =
      seibergWittenSolutionInvariant data solution :=
  data.curvatureGaugeInvariant u solution.1.1

/-- A one-parameter Abelian gauge flow. -/
structure SeibergWittenGaugeFlow
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms) where
  phase : ℝ → Circle
  phase_zero : phase 0 = 1
  phase_add : ∀ s t, phase (s + t) = phase s * phase t

/-- Time-`t` action of a Seiberg--Witten gauge flow on exact solutions. -/
def SeibergWittenGaugeFlow.at
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    {data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms}
    (flow : SeibergWittenGaugeFlow data) (t : ℝ) :
    SeibergWittenSolution data → SeibergWittenSolution data :=
  gaugeTransformSolution data (flow.phase t)

/-- The self-dual curvature invariant is constant at every time along a gauge flow. -/
theorem SeibergWittenGaugeFlow.at_invariant
    {Connection PositiveSpinor NegativeSpinor TwoForms : Type*}
    [AddCommGroup PositiveSpinor] [Module ℂ PositiveSpinor]
    [AddCommGroup NegativeSpinor] [Module ℂ NegativeSpinor]
    [AddCommGroup TwoForms] [Module ℝ TwoForms]
    {data : SeibergWittenData Connection PositiveSpinor NegativeSpinor TwoForms}
    (flow : SeibergWittenGaugeFlow data) (t : ℝ) (solution : SeibergWittenSolution data) :
    seibergWittenSolutionInvariant data (flow.at t solution) =
      seibergWittenSolutionInvariant data solution :=
  gaugeTransformSolution_invariant data (flow.phase t) solution

end GaloisForLFunctions.HTGeometry.SeibergWitten
