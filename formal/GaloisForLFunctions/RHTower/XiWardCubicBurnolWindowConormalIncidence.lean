import GaloisForLFunctions.RHTower.BurnolCoPoissonConormalReflectionCover
import GaloisForLFunctions.RHTower.XiWardCubicRawConormalModularDoublet

/-!
# Cubic Ward/Burnol window--conormal incidence

This file identifies two independently constructed coordinates on the completed Xi divisor.
Burnol's exact-order nested-window quotient gives the centered aperture character
`exp (L * (rho - 1 / 2))`.  Inverting that character and applying the conormal clock `L`
produces exactly the base residue feature of the completed-Xi logarithmic conormal column.

Functional-equation reflection supplies the adjoint mate rather than a second positive-half-line
copy.  Their aperture pairing is therefore the cubic Ward self-charge
`1 / (4 * (rho.re - 1 / 2)^(3 : ℕ))`.  This closes support-level incidence between source-defined
Burnol aperture tomography and the completed-Xi conormal residue; no norm contraction from the
Euler source is asserted here.
-/

open Complex Set Filter Topology MeasureTheory

namespace RHTower

noncomputable section

/-- Inverse centered Burnol window character with one conormal clock factor. -/
def xiWardCubicBurnolWindowConormalFeature (L : ℝ) (rho : ℂ) : ℂ :=
  (L : ℂ) * (burnolCoPoissonCenteredConormalCharacter L rho)⁻¹

/-- The Burnol inverse-window feature is literally the completed-Xi base conormal residue
feature, before restricting `rho` to the Xi divisor. -/
theorem xiWardCubicBurnolWindowConormalFeature_eq
    (L : ℝ) (rho : ℂ) :
    xiWardCubicBurnolWindowConormalFeature L rho =
      routePXiBaseConormalResidueFeature rho L := by
  rw [xiWardCubicBurnolWindowConormalFeature,
    burnolCoPoissonCenteredConormalCharacter,
    routePXiBaseConormalResidueFeature, ← Complex.exp_neg]
  congr 1
  ring

/-- Centered coordinate extracted from Burnol's actual doubled nested-window top-conormal ratio. -/
def xiWardCubicBurnolActualCenteredWindowCoordinate
    (L : ℝ) (rho : XiDivisorSupport) : ℂ :=
  Complex.exp (-(L : ℂ) / 2) *
    burnolCoPoissonActualDoubledWindowConormalRatio L rho

/-- At every positive aperture, the actual quotient top-jet ratio is the centered conormal
character. -/
theorem xiWardCubicBurnolActualCenteredWindowCoordinate_eq
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    xiWardCubicBurnolActualCenteredWindowCoordinate L rho =
      burnolCoPoissonCenteredConormalCharacter L (rho : ℂ) := by
  rw [xiWardCubicBurnolActualCenteredWindowCoordinate,
    burnolCoPoissonActualDoubledWindowConormalRatio_eq_exp hL,
    burnolCoPoissonCenteredConormalCharacter, ← Complex.exp_add]
  congr 1
  ring

/-- The actual Burnol quotient coordinate, inverted and conormally differentiated. -/
def xiWardCubicBurnolActualConormalFeature
    (L : ℝ) (rho : XiDivisorSupport) : ℂ :=
  (L : ℂ) *
    (xiWardCubicBurnolActualCenteredWindowCoordinate L rho)⁻¹

/-- Actual source-window top-conormal tomography equals the completed-Xi residue feature. -/
theorem xiWardCubicBurnolActualConormalFeature_eq
    {L : ℝ} (hL : 0 < L) (rho : XiDivisorSupport) :
    xiWardCubicBurnolActualConormalFeature L rho =
      routePXiBaseConormalResidueFeature (rho : ℂ) L := by
  rw [xiWardCubicBurnolActualConormalFeature,
    xiWardCubicBurnolActualCenteredWindowCoordinate_eq hL]
  exact xiWardCubicBurnolWindowConormalFeature_eq L (rho : ℂ)

/-- Functional-equation reflected Burnol character carrying the opposite conormal orientation. -/
def xiWardCubicBurnolReflectedWindowMate (L : ℝ) (rho : ℂ) : ℂ :=
  (L : ℂ) * burnolCoPoissonCenteredConormalCharacter L
    (burnolCoPoissonConormalReflection rho)

/-- The reflected orientation is exactly the Hermitian adjoint of the forward inverse-window
feature. -/
theorem xiWardCubicBurnolReflectedWindowMate_eq_star
    (L : ℝ) (rho : ℂ) :
    xiWardCubicBurnolReflectedWindowMate L rho =
      star (xiWardCubicBurnolWindowConormalFeature L rho) := by
  rw [xiWardCubicBurnolReflectedWindowMate,
    burnolCoPoissonCenteredConormalCharacter_reflection,
    xiWardCubicBurnolWindowConormalFeature]
  simp

/-- The continuous aperture trace of the forward/reflected Burnol pair is the exact cubic
self-charge at a strict-right point. -/
theorem integral_xiWardCubicBurnolWindowConormalFeature_mul_reflectedMate
    {rho : ℂ} (hrho : 1 / 2 < rho.re) :
    (∫ L : ℝ in Ioi 0,
      xiWardCubicBurnolWindowConormalFeature L rho *
        xiWardCubicBurnolReflectedWindowMate L rho) =
      (((1 : ℝ) / (4 * (rho.re - 1 / 2) ^ (3 : ℕ)) : ℝ) : ℂ) := by
  rw [show (fun L : ℝ =>
      xiWardCubicBurnolWindowConormalFeature L rho *
        xiWardCubicBurnolReflectedWindowMate L rho) =
      fun L : ℝ => routePXiBaseConormalResidueFeature rho L *
        xiWardCubicReflectedConormalMateFeature rho L by
    funext L
    rw [xiWardCubicBurnolWindowConormalFeature_eq,
      xiWardCubicBurnolReflectedWindowMate_eq_star,
      xiWardCubicBurnolWindowConormalFeature_eq,
      xiWardCubicReflectedConormalMateFeature_eq_star]]
  exact integral_routePXiBaseConormalResidueFeature_mul_reflectedMate hrho

/-- The normalized residue of the completed-Xi conormal column is the actual Burnol
nested-window conormal feature at every positive aperture. -/
theorem routePCompletedXiConormalColumn_normalized_residue_eq_burnolWindow
    (rho : XiDivisorSupport) {L : ℝ} (hL : 0 < L) :
    Tendsto
      (fun z : ℂ =>
        ((z - (rho : ℂ)) * routePCompletedXiConormalColumn z L) /
          ((analyticOrderAt xi (rho : ℂ)).toNat : ℂ))
      (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (nhds (xiWardCubicBurnolActualConormalFeature L rho)) := by
  rw [xiWardCubicBurnolActualConormalFeature_eq hL]
  exact routePCompletedXiConormalColumn_normalized_residue
    (xi_eq_zero_of_mem_divisor_support rho) L

end

end RHTower
