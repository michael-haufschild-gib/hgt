import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Left-Weyl bridge into the finite Seiberg--Witten spinor skeleton

`HLSPhysicalAssumptions` provides a four-component Dirac carrier as a pair of Weyl components.
This module restricts to its left component and applies the finite Abelian spinor--curvature map.
It is a chiral algebraic bridge only: it does not turn the HLS representation data into a
four-manifold Seiberg--Witten system.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A complex-valued HLS Dirac spinor in the Weyl decomposition. -/
abbrev HLSDiracSpinorField := HLSDiracSpinor → ℂ

/-- Left-handed Weyl component of an HLS Dirac spinor. -/
def hlsLeftWeylSpinor (Ψ : HLSDiracSpinorField) : SeibergWittenSpinor :=
  fun i => Ψ (.inl i)

/-- The finite Abelian spinor--curvature invariant of the left Weyl component. -/
def hlsLeftWeylSeibergWittenInvariant (Ψ : HLSDiracSpinorField) :
    SeibergWittenCurvature :=
  seibergWittenInvariant (hlsLeftWeylSpinor Ψ)

/-- Left-Weyl restriction commutes with the common Abelian phase action. -/
theorem hlsLeftWeylSpinor_gaugeEquivariant (u : Circle) (Ψ : HLSDiracSpinorField) :
    hlsLeftWeylSpinor (u • Ψ) = u • hlsLeftWeylSpinor Ψ := by
  funext i
  simp [hlsLeftWeylSpinor]

/-- The HLS left-Weyl finite Seiberg--Witten invariant is phase-gauge invariant. -/
theorem hlsLeftWeylSeibergWittenInvariant_gaugeInvariant
    (u : Circle) (Ψ : HLSDiracSpinorField) :
    hlsLeftWeylSeibergWittenInvariant (u • Ψ) =
      hlsLeftWeylSeibergWittenInvariant Ψ := by
  rw [hlsLeftWeylSeibergWittenInvariant, hlsLeftWeylSpinor_gaugeEquivariant]
  exact seibergWittenInvariant_gaugeInvariant u (hlsLeftWeylSpinor Ψ)

/-- The induced left-Weyl curvature solves the finite algebraic spinor--curvature equation. -/
theorem hlsLeftWeyl_seibergWittenEquation (Ψ : HLSDiracSpinorField) :
    seibergWittenEquation (hlsLeftWeylSeibergWittenInvariant Ψ) (hlsLeftWeylSpinor Ψ) :=
  seibergWittenEquation_inducedCurvature (hlsLeftWeylSpinor Ψ)

/-- The HLS left-Weyl finite curvature record is Hermitian. -/
theorem hlsLeftWeylSeibergWittenInvariant_isHermitian (Ψ : HLSDiracSpinorField) :
    (hlsLeftWeylSeibergWittenInvariant Ψ).IsHermitian :=
  seibergWittenInvariant_isHermitian (hlsLeftWeylSpinor Ψ)

/-- Every HLS left-Weyl finite curvature record has zero determinant. -/
theorem hlsLeftWeylSeibergWittenInvariant_det_eq_zero (Ψ : HLSDiracSpinorField) :
    (hlsLeftWeylSeibergWittenInvariant Ψ).det = 0 :=
  seibergWittenInvariant_det_eq_zero (hlsLeftWeylSpinor Ψ)

/-- The HLS left-Weyl invariant is constant along any common-phase gauge flow. -/
theorem hlsLeftWeylSeibergWittenGaugeFlow_invariant
    (phase : ℝ → Circle) (t : ℝ) (Ψ : HLSDiracSpinorField) :
    hlsLeftWeylSeibergWittenInvariant (phase t • Ψ) =
      hlsLeftWeylSeibergWittenInvariant Ψ :=
  hlsLeftWeylSeibergWittenInvariant_gaugeInvariant (phase t) Ψ

end GaloisForLFunctions.HTGeometry
