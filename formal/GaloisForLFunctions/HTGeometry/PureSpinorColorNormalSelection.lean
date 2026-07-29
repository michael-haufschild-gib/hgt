import GaloisForLFunctions.HTGeometry.PurePairNormalFracture

/-!
# Colour-cancellation selection in the pure-spinor second fundamental form

At the standard pure spinor, split the two-form tangent coordinates according to
`ℂ⁵ = ℂ³ ⊕ ℂ²` into:

* a colour bivector `Λ²ℂ³`;
* a mixed colour--weak tensor `ℂ³ ⊗ ℂ²`;
* a weak scalar `Λ²ℂ²`.

This file proves directly from the Cartan quadrics that the colourless two-component normal
reporter vanishes on every same-sector pair and on every pair containing the weak scalar.  Its
only nonzero sector is colour-bivector times colour--weak, and fixing any nonzero colour
bivector makes that pairing surjective onto the complete colourless normal doublet.

These are unconditional finite-dimensional coordinate identities.  No actualization, Higgs
field, spacetime, gravity, or physical interpretation is assumed.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Three complex coordinates of the colour bivector `Λ²ℂ³`. -/
abbrev PureSpinorColorBivector := Fin 3 → ℂ

/-- Six complex coordinates of the mixed colour--weak tangent sector `ℂ³ ⊗ ℂ²`. -/
abbrev PureSpinorColorWeakTangent := Fin 3 → Fin 2 → ℂ

/-- Cartan two-form tangent supported on the colour bivector sector. -/
def pureSpinorColorTangent
    (c : PureSpinorColorBivector) : SpinTenEvenCoordinate :=
  (0,
    ![![0, c 0, c 1, 0, 0],
      ![-c 0, 0, c 2, 0, 0],
      ![-c 1, -c 2, 0, 0, 0],
      ![0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0]],
    0)

/-- Cartan two-form tangent supported on the mixed colour--weak sector. -/
def pureSpinorColorWeakTangentVariation
    (m : PureSpinorColorWeakTangent) : SpinTenEvenCoordinate :=
  (0,
    ![![0, 0, 0, m 0 0, m 0 1],
      ![0, 0, 0, m 1 0, m 1 1],
      ![0, 0, 0, m 2 0, m 2 1],
      ![-m 0 0, -m 1 0, -m 2 0, 0, 0],
      ![-m 0 1, -m 1 1, -m 2 1, 0, 0]],
    0)

/-- Cartan two-form tangent supported on the weak scalar `Λ²ℂ²`. -/
def pureSpinorWeakScalarTangent (z : ℂ) : SpinTenEvenCoordinate :=
  (0,
    ![![0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0],
      ![0, 0, 0, 0, 0],
      ![0, 0, 0, 0, z],
      ![0, 0, 0, -z, 0]],
    0)

/-- Last two upper Cartan-polar coordinates: the colourless normal doublet reporter. -/
def pureSpinorColorlessNormalSecondFundamental
    (x y : SpinTenEvenCoordinate) : ColorPreservingNormal :=
  ![(spinTenCartanPolar x y).1 3, (spinTenCartanPolar x y).1 4]

/-- Explicit colour-bivector by colour--weak normal pairing. -/
def pureSpinorColorMixedNormalPairing
    (c : PureSpinorColorBivector)
    (m : PureSpinorColorWeakTangent) : ColorPreservingNormal :=
  ![-c 0 * m 2 1 + c 1 * m 1 1 - c 2 * m 0 1,
    c 0 * m 2 0 - c 1 * m 1 0 + c 2 * m 0 0]

/-- The explicit pairing is exactly the colourless part of the polarized Cartan quadrics. -/
theorem pureSpinorColorlessNormal_color_mixed_eq
    (c : PureSpinorColorBivector)
    (m : PureSpinorColorWeakTangent) :
    pureSpinorColorlessNormalSecondFundamental
        (pureSpinorColorTangent c)
        (pureSpinorColorWeakTangentVariation m) =
      pureSpinorColorMixedNormalPairing c m := by
  funext i
  fin_cases i <;>
    simp [pureSpinorColorlessNormalSecondFundamental,
      pureSpinorColorMixedNormalPairing, pureSpinorColorTangent,
      pureSpinorColorWeakTangentVariation, spinTenCartanPolar,
      spinTenCartanQuadrics, spinTenCartanUpper, spinTenScalar,
      spinTenTwo, spinTenFour] <;>
    ring

/-- Symmetry of the Cartan polar gives the same pairing in the reverse sector order. -/
theorem pureSpinorColorlessNormal_mixed_color_eq
    (c : PureSpinorColorBivector)
    (m : PureSpinorColorWeakTangent) :
    pureSpinorColorlessNormalSecondFundamental
        (pureSpinorColorWeakTangentVariation m)
        (pureSpinorColorTangent c) =
      pureSpinorColorMixedNormalPairing c m := by
  funext i
  fin_cases i <;>
    simp [pureSpinorColorlessNormalSecondFundamental,
      pureSpinorColorMixedNormalPairing, pureSpinorColorTangent,
      pureSpinorColorWeakTangentVariation, spinTenCartanPolar,
      spinTenCartanQuadrics, spinTenCartanUpper, spinTenScalar,
      spinTenTwo, spinTenFour] <;>
    ring

/-- Two colour-bivector tangents have zero colourless normal reporter. -/
theorem pureSpinorColorlessNormal_color_color_eq_zero
    (c d : PureSpinorColorBivector) :
    pureSpinorColorlessNormalSecondFundamental
        (pureSpinorColorTangent c) (pureSpinorColorTangent d) = 0 := by
  funext i
  fin_cases i <;>
    simp [pureSpinorColorlessNormalSecondFundamental,
      pureSpinorColorTangent, spinTenCartanPolar, spinTenCartanQuadrics,
      spinTenCartanUpper, spinTenScalar, spinTenTwo, spinTenFour]

/-- Two mixed colour--weak tangents have zero colourless normal reporter. -/
theorem pureSpinorColorlessNormal_mixed_mixed_eq_zero
    (m n : PureSpinorColorWeakTangent) :
    pureSpinorColorlessNormalSecondFundamental
        (pureSpinorColorWeakTangentVariation m)
        (pureSpinorColorWeakTangentVariation n) = 0 := by
  funext i
  fin_cases i <;>
    simp [pureSpinorColorlessNormalSecondFundamental,
      pureSpinorColorWeakTangentVariation, spinTenCartanPolar,
      spinTenCartanQuadrics, spinTenCartanUpper, spinTenScalar,
      spinTenTwo, spinTenFour]

/-- A weak-scalar tangent cannot contribute to the colourless normal reporter against any
Cartan coordinate variation. -/
theorem pureSpinorColorlessNormal_weakScalar_left_eq_zero
    (z : ℂ) (x : SpinTenEvenCoordinate) :
    pureSpinorColorlessNormalSecondFundamental
        (pureSpinorWeakScalarTangent z) x = 0 := by
  funext i
  fin_cases i <;>
    simp [pureSpinorColorlessNormalSecondFundamental,
      pureSpinorWeakScalarTangent, spinTenCartanPolar,
      spinTenCartanQuadrics, spinTenCartanUpper, spinTenScalar,
      spinTenTwo, spinTenFour]

/-- The weak-scalar vanishing also holds in the reverse sector order. -/
theorem pureSpinorColorlessNormal_weakScalar_right_eq_zero
    (z : ℂ) (x : SpinTenEvenCoordinate) :
    pureSpinorColorlessNormalSecondFundamental
        x (pureSpinorWeakScalarTangent z) = 0 := by
  funext i
  fin_cases i <;>
    simp [pureSpinorColorlessNormalSecondFundamental,
      pureSpinorWeakScalarTangent, spinTenCartanPolar,
      spinTenCartanQuadrics, spinTenCartanUpper, spinTenScalar,
      spinTenTwo, spinTenFour]

/-- Fixing any nonzero colour bivector makes the colour--mixed Cartan pairing surjective onto
the full colourless normal doublet. -/
theorem pureSpinorColorMixedNormalPairing_surjective
    (c : PureSpinorColorBivector) (hc : c ≠ 0) :
    Function.Surjective (pureSpinorColorMixedNormalPairing c) := by
  intro w
  by_cases h0 : c 0 = 0
  · by_cases h1 : c 1 = 0
    · have h2 : c 2 ≠ 0 := by
        intro h2
        apply hc
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨![![w 1 / c 2, -w 0 / c 2], ![0, 0], ![0, 0]], ?_⟩
      funext i
      fin_cases i <;>
        simp [pureSpinorColorMixedNormalPairing, h0, h1] <;>
        field_simp
    · refine ⟨![![0, 0], ![-w 1 / c 1, w 0 / c 1], ![0, 0]], ?_⟩
      funext i
      fin_cases i <;>
        simp [pureSpinorColorMixedNormalPairing, h0] <;>
        field_simp
  · refine ⟨![![0, 0], ![0, 0], ![w 1 / c 0, -w 0 / c 0]], ?_⟩
    funext i
    fin_cases i <;>
      simp [pureSpinorColorMixedNormalPairing] <;>
      field_simp

end GaloisForLFunctions.HTGeometry
