import GaloisForLFunctions.HTGeometry.SeibergWitten.Gauge
import GaloisForLFunctions.HTGeometry.SeibergWitten.FlatConnection
import GaloisForLFunctions.HTGeometry.SeibergWittenSelfDualCurvature

/-!
# A nonstationary flat Seiberg--Witten gauge flow

The spatially constant phase `exp(it)` is a closed one-parameter `U(1)` gauge flow on Euclidean
four-space.  It acts on constant sections of the actual flat positive spinor bundle, and the
trace-free self-dual curvature constructed from those sections is constant along the flow.

The current gauge API does not package smoothness of maps to the manifold `Circle`; this module
therefore proves the exact group action and curvature invariance, without asserting that missing
smooth-map layer.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Standard unit complex phase `exp(it)`. -/
def seibergWittenUnitPhase (t : ℝ) : Circle :=
  ⟨Complex.exp ((t : ℂ) * Complex.I), by
    simp [Submonoid.unitSphere, Complex.norm_exp]⟩

/-- The phase at time zero is the identity. -/
theorem seibergWittenUnitPhase_zero : seibergWittenUnitPhase 0 = 1 := by
  apply Subtype.ext
  simp [seibergWittenUnitPhase]

/-- The standard phase obeys the one-parameter group law. -/
theorem seibergWittenUnitPhase_add (s t : ℝ) :
    seibergWittenUnitPhase (s + t) =
      seibergWittenUnitPhase s * seibergWittenUnitPhase t := by
  apply Subtype.ext
  simp [seibergWittenUnitPhase, add_mul, Complex.exp_add]

/-- Spatially constant `exp(it)` gauge flow on the flat four-model. -/
def flatSeibergWittenGaugeFlow : SeibergWitten.U1GaugeFlow SeibergWitten.FourSpace where
  phase := fun t _ => seibergWittenUnitPhase t
  phase_zero := by
    funext x
    exact seibergWittenUnitPhase_zero
  phase_add := by
    intro s t
    funext x
    exact seibergWittenUnitPhase_add s t

/-- Constant section of the flat positive spinor bundle. -/
def flatConstantSpinorSection (psi : SeibergWittenSpinor) :
    ∀ x : SeibergWitten.FourSpace, SeibergWitten.flatPositiveSpinorBundle x :=
  fun _ => psi

/-- Every point on the phase orbit of a constant spinor solves the flat chiral Dirac equation. -/
theorem flatSeibergWittenGaugeFlow_dirac
    (t : ℝ) (psi : SeibergWittenSpinor) (x : SeibergWitten.FourSpace) :
    SeibergWitten.flatChiralDirac SeibergWitten.flatPositiveSpinorConnection
      (flatSeibergWittenGaugeFlow.actOnSpinor t (flatConstantSpinorSection psi)) x = 0 := by
  change SeibergWitten.flatChiralDirac SeibergWitten.flatPositiveSpinorConnection
    (SeibergWitten.flatConstantPositiveSpinorSection (seibergWittenUnitPhase t • psi)) x = 0
  exact SeibergWitten.flatChiralDirac_flatConstant _ _

/-- The nonstationary phase orbit stays inside the kernel of the actual flat chiral Dirac
operator. -/
theorem flatSeibergWittenGaugeFlow_solves_flatChiralDiracEquation
    (t : ℝ) (psi : SeibergWittenSpinor) :
    SeibergWitten.flatChiralDiracEquation
      (flatSeibergWittenGaugeFlow.actOnSpinor t (flatConstantSpinorSection psi)) :=
  fun x => flatSeibergWittenGaugeFlow_dirac t psi x

/-- The flat nonstationary gauge flow preserves self-dual curvature at every point and time. -/
theorem flatSeibergWittenGaugeFlow_selfDualInvariant
    (t : ℝ) (psi : SeibergWittenSpinor) (x : SeibergWitten.FourSpace) :
    seibergWittenSelfDualCurvature
      (flatSeibergWittenGaugeFlow.actOnSpinor t (flatConstantSpinorSection psi) x) =
    seibergWittenSelfDualCurvature psi := by
  change seibergWittenSelfDualCurvature (seibergWittenUnitPhase t • psi) =
    seibergWittenSelfDualCurvature psi
  exact seibergWittenSelfDualCurvature_gaugeInvariant _ _

end GaloisForLFunctions.HTGeometry
