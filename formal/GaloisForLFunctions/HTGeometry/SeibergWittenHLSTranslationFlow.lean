import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions
import GaloisForLFunctions.HTGeometry.SeibergWittenHLSChiralBridge

/-!
# HLS translation characters as finite Seiberg--Witten gauge flows

For fixed Minkowski momentum and translation direction, the HLS infrastructure provides the
unit-modulus character `exp(-i⟨p,x⟩)`.  This module promotes it to `Circle`, proves its zero and
addition laws along a real translation ray, and uses it as the phase in the finite
Seiberg--Witten flow.  The finite curvature invariant, including its existing left-Weyl HLS
restriction, is therefore constant along this physically named phase flow.

This transports an exact character law only.  It does not establish a coupled field equation for
an HLS representation or equate spacetime translation with a gauge transformation in continuum
Seiberg--Witten theory.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The unit-modulus HLS translation character as a point of the complex circle. -/
def hlsTranslationCircle (p x : HLSMinkowskiVector) : Circle :=
  ⟨hlsTranslationPhase p x, by
    simpa [Submonoid.unitSphere] using hlsTranslationPhase_norm p x⟩

/-- The translation phase is trivial at the origin. -/
theorem hlsTranslationCircle_zero (p : HLSMinkowskiVector) : hlsTranslationCircle p 0 = 1 := by
  apply Subtype.ext
  exact hlsTranslationPhase_zero p

/-- Translation addition becomes multiplication in the gauge circle. -/
theorem hlsTranslationCircle_add (p x y : HLSMinkowskiVector) :
    hlsTranslationCircle p (x + y) = hlsTranslationCircle p x * hlsTranslationCircle p y := by
  apply Subtype.ext
  exact hlsTranslationPhase_add p x y

/-- One-parameter gauge phase obtained by restricting an HLS translation character to a ray. -/
def hlsTranslationCircleFlow (p x : HLSMinkowskiVector) : ℝ → Circle :=
  fun t => hlsTranslationCircle p (t • x)

/-- The HLS translation phase flow starts at the identity. -/
theorem hlsTranslationCircleFlow_zero (p x : HLSMinkowskiVector) :
    hlsTranslationCircleFlow p x 0 = 1 := by
  simpa [hlsTranslationCircleFlow] using hlsTranslationCircle_zero p

/-- The HLS translation phase flow is multiplicative in its real time parameter. -/
theorem hlsTranslationCircleFlow_add (p x : HLSMinkowskiVector) (s t : ℝ) :
    hlsTranslationCircleFlow p x (s + t) =
      hlsTranslationCircleFlow p x s * hlsTranslationCircleFlow p x t := by
  unfold hlsTranslationCircleFlow
  rw [add_smul, hlsTranslationCircle_add]

/-- Finite Seiberg--Witten phase flow driven by an HLS translation character. -/
def hlsTranslationSeibergWittenFlow
    (p x : HLSMinkowskiVector) (psi : SeibergWittenSpinor) : ℝ → SeibergWittenSpinor :=
  seibergWittenGaugeFlow (hlsTranslationCircleFlow p x) psi

/-- The finite Seiberg--Witten invariant is constant along every HLS translation phase flow. -/
theorem hlsTranslationSeibergWittenFlow_invariant
    (p x : HLSMinkowskiVector) (psi : SeibergWittenSpinor) (t : ℝ) :
    seibergWittenInvariant (hlsTranslationSeibergWittenFlow p x psi t) =
      seibergWittenInvariant psi := by
  exact seibergWittenGaugeFlow_invariant (hlsTranslationCircleFlow p x) t psi

/-- The corresponding HLS Dirac-spinor phase flow. -/
def hlsChiralTranslationSeibergWittenFlow
    (p x : HLSMinkowskiVector) (Psi : HLSDiracSpinorField) : ℝ → HLSDiracSpinorField :=
  fun t => hlsTranslationCircleFlow p x t • Psi

/-- The left-Weyl finite invariant is constant along the HLS translation phase flow. -/
theorem hlsChiralTranslationSeibergWittenFlow_invariant
    (p x : HLSMinkowskiVector) (Psi : HLSDiracSpinorField) (t : ℝ) :
    hlsLeftWeylSeibergWittenInvariant
      (hlsChiralTranslationSeibergWittenFlow p x Psi t) =
      hlsLeftWeylSeibergWittenInvariant Psi := by
  exact hlsLeftWeylSeibergWittenInvariant_gaugeInvariant
    (hlsTranslationCircleFlow p x t) Psi

end GaloisForLFunctions.HTGeometry
