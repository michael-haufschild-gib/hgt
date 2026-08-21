import GaloisForLFunctions.HTGeometry.SeibergWitten.Equations

/-!
# Closed consistency model for the Seiberg--Witten equation interfaces

The model below has zero spinor and form spaces.  It is deliberately a closed algebraic
consistency model, rather than a geometric claim about a nontrivial four-manifold.  Its value is
mechanical: it proves that the smooth/Clifford/Hodge/Dirac interface admits an unconditional
solution and a gauge flow without axioms or unfinished proof obligations.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Zero positive-spinor section space used by the closed consistency model. -/
abbrev ZeroPositiveSpinor := Fin 0 → ℂ

/-- Zero negative-spinor section space used by the closed consistency model. -/
abbrev ZeroNegativeSpinor := Fin 0 → ℂ

/-- Zero two-form space used by the closed consistency model. -/
abbrev ZeroTwoForms := Fin 0 → ℝ

/-- Identity Hodge star on the zero two-form space. -/
def zeroHodgeStar : HodgeStar ZeroTwoForms where
  toLinearMap := LinearMap.id
  sq := rfl

/-- Closed zero-field Seiberg--Witten geometric data. -/
def zeroSeibergWittenData :
    SeibergWittenData PUnit ZeroPositiveSpinor ZeroNegativeSpinor ZeroTwoForms where
  hodgeStar := zeroHodgeStar
  curvature := fun _ => 0
  dirac := fun _ => 0
  quadraticMap := fun _ => 0
  quadraticMap_selfDual := by intro; rfl
  gaugeConnection := fun _ A => A
  curvatureGaugeInvariant := by
    intro
    simp [HodgeStar.selfDualPart, zeroHodgeStar]
  diracGaugeCovariant := by
    intro
    simp
  quadraticMap_gaugeInvariant := by
    intro u ψ
    rfl

/-- The zero configuration is an exact closed solution of both coupled equations. -/
def zeroSeibergWittenSolution : SeibergWittenSolution zeroSeibergWittenData :=
  ⟨(PUnit.unit, 0), by
    constructor
    · rfl
    · simp [zeroSeibergWittenData, zeroHodgeStar, HodgeStar.selfDualPart]⟩

/-- Every `U(1)` phase fixes the closed zero-field solution. -/
theorem zeroSeibergWittenSolution_gaugeFixed (u : Circle) :
    gaugeTransformSolution zeroSeibergWittenData u zeroSeibergWittenSolution =
      zeroSeibergWittenSolution := by
  apply Subtype.ext
  exact Prod.ext rfl (smul_zero _)

/-- The closed zero-field solution has zero self-dual curvature invariant. -/
theorem zeroSeibergWittenSolution_invariant :
    seibergWittenSolutionInvariant zeroSeibergWittenData zeroSeibergWittenSolution = 0 := by
  simp [seibergWittenSolutionInvariant, zeroSeibergWittenData, zeroHodgeStar,
    HodgeStar.selfDualPart]

/-- Stationary Abelian gauge flow in the closed zero-field model. -/
def zeroSeibergWittenGaugeFlow : SeibergWittenGaugeFlow zeroSeibergWittenData where
  phase := fun _ => 1
  phase_zero := rfl
  phase_add := by intro; simp

/-- The zero-field invariant remains zero at every gauge-flow time. -/
theorem zeroSeibergWittenGaugeFlow_invariant (t : ℝ) :
    seibergWittenSolutionInvariant zeroSeibergWittenData
      (zeroSeibergWittenGaugeFlow.at t zeroSeibergWittenSolution) = 0 := by
  rw [zeroSeibergWittenGaugeFlow.at_invariant]
  exact zeroSeibergWittenSolution_invariant

end GaloisForLFunctions.HTGeometry.SeibergWitten
