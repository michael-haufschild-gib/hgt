import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSourcePositiveClosure
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Hidden sl₂ structure of the source-positive rank-three flow

The autonomous `(U,B,Q)` theta-source vector field belongs to an exact polynomial `sl₂`
triple.  The lowering-adapted coordinates `r=U+3B`, `b=B`, and
`k=Q+3/8-3B²/8` make the companion lowering field equal to `∂b` while preserving `r` and `k`.
These are unconditional polynomial identities; no numerical certificate enters the proofs.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Coordinate formula for the bracket of two rank-three polynomial vector fields. -/
def modularThetaSourcePositiveVectorFieldBracket
    (X Y : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial) :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial :=
  fun i =>
    (MvPolynomial.pderiv .U (Y i) * X .U -
      MvPolynomial.pderiv .U (X i) * Y .U) +
    (MvPolynomial.pderiv .B (Y i) * X .B -
      MvPolynomial.pderiv .B (X i) * Y .B) +
    (MvPolynomial.pderiv .Q (Y i) * X .Q -
      MvPolynomial.pderiv .Q (X i) * Y .Q)

/-- Cartan scale field before multiplication by four. -/
def modularThetaSourcePositiveScaleField :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial
  | .U => MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .U
  | .B => MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B
  | .Q => MvPolynomial.X .Q + MvPolynomial.C (3 / 8 : ℂ)

/-- Lowering field which becomes `∂b` in the adapted coordinates. -/
def modularThetaSourcePositiveLoweringField :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial
  | .U => MvPolynomial.C (-3 : ℂ)
  | .B => MvPolynomial.C (1 : ℂ)
  | .Q => MvPolynomial.C (3 / 4 : ℂ) * MvPolynomial.X .B

/-- Raising element: source dynamics plus the lowering field. -/
def modularThetaSourcePositiveSl2E :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial :=
  fun i => modularThetaSourcePositiveVectorField i +
    modularThetaSourcePositiveLoweringField i

/-- Lowering element with the standard `sl₂` sign convention. -/
def modularThetaSourcePositiveSl2F :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial :=
  fun i => -modularThetaSourcePositiveLoweringField i

/-- Cartan element: four times the scale field. -/
def modularThetaSourcePositiveSl2H :
    ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial :=
  fun i => MvPolynomial.C (4 : ℂ) * modularThetaSourcePositiveScaleField i

/-- Lowering-invariant horizontal coordinate `r=U+3B`. -/
def modularThetaSourcePositiveSl2R : ModularThetaSourcePositivePolynomial :=
  MvPolynomial.X .U + MvPolynomial.C (3 : ℂ) * MvPolynomial.X .B

/-- One sixteenth of the reconstructed source-positive gap. -/
def modularThetaSourcePositiveSl2K : ModularThetaSourcePositivePolynomial :=
  MvPolynomial.X .Q + MvPolynomial.C (3 / 8 : ℂ) -
    MvPolynomial.C (3 / 8 : ℂ) * MvPolynomial.X .B ^ (2 : ℕ)

/-- Lie derivative along an arbitrary rank-three polynomial field. -/
def modularThetaSourcePositiveFieldLie
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (P : ModularThetaSourcePositivePolynomial) : ModularThetaSourcePositivePolynomial :=
  MvPolynomial.pderiv .U P * X .U +
    MvPolynomial.pderiv .B P * X .B +
    MvPolynomial.pderiv .Q P * X .Q

/-- In `(r,b,k)` coordinates the companion lowering field is exactly `∂b`. -/
theorem modularThetaSourcePositiveLoweringField_coordinates :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveLoweringField
        modularThetaSourcePositiveSl2R = 0 ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveLoweringField
        (MvPolynomial.X .B) = 1 ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveLoweringField
        modularThetaSourcePositiveSl2K = 0 := by
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveLoweringField, modularThetaSourcePositiveSl2R]
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveLoweringField]
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveLoweringField, modularThetaSourcePositiveSl2K]
    ring

/-- The scale field gives weights `1/2,1/2,1` to `(r,b,k)`. -/
theorem modularThetaSourcePositiveScaleField_coordinates :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveScaleField
        modularThetaSourcePositiveSl2R =
          MvPolynomial.C (1 / 2 : ℂ) * modularThetaSourcePositiveSl2R ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveScaleField
          (MvPolynomial.X .B) =
            MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.X .B ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveScaleField
          modularThetaSourcePositiveSl2K = modularThetaSourcePositiveSl2K := by
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveScaleField, modularThetaSourcePositiveSl2R]
    ring
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveScaleField]
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveScaleField, modularThetaSourcePositiveSl2K]
    ring

/-- Exact source dynamics in the lowering-adapted coordinates `(r,b,k)`. -/
theorem modularThetaSourcePositiveVectorField_coordinates :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveVectorField
        modularThetaSourcePositiveSl2R =
        MvPolynomial.C (2 : ℂ) * MvPolynomial.X .B *
            modularThetaSourcePositiveSl2R +
          MvPolynomial.C (16 : ℂ) * modularThetaSourcePositiveSl2K ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveVectorField
          (MvPolynomial.X .B) =
        MvPolynomial.X .B ^ (2 : ℕ) +
          MvPolynomial.C (4 : ℂ) * modularThetaSourcePositiveSl2K - 1 ∧
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveVectorField
          modularThetaSourcePositiveSl2K =
        MvPolynomial.C (4 : ℂ) * MvPolynomial.X .B *
            modularThetaSourcePositiveSl2K -
          MvPolynomial.C (2 : ℂ) * modularThetaSourcePositiveSl2K *
            modularThetaSourcePositiveSl2R := by
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveVectorField, modularThetaSourcePositiveGap,
      modularThetaSourcePositiveSl2R, modularThetaSourcePositiveSl2K]
    ring
  constructor
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveVectorField, modularThetaSourcePositiveGap,
      modularThetaSourcePositiveSl2K]
    ring
  · apply MvPolynomial.funext
    intro v
    simp [modularThetaSourcePositiveFieldLie,
      modularThetaSourcePositiveVectorField, modularThetaSourcePositiveGap,
      modularThetaSourcePositiveSl2R, modularThetaSourcePositiveSl2K]
    ring

/-- First standard `sl₂` bracket: `[h,e]=2e`. -/
theorem modularThetaSourcePositive_sl2_bracket_he :
    modularThetaSourcePositiveVectorFieldBracket
      modularThetaSourcePositiveSl2H modularThetaSourcePositiveSl2E =
      fun i => MvPolynomial.C (2 : ℂ) * modularThetaSourcePositiveSl2E i := by
  funext i
  cases i <;>
    apply MvPolynomial.funext <;>
    intro v <;>
    simp [modularThetaSourcePositiveVectorFieldBracket,
      modularThetaSourcePositiveSl2H, modularThetaSourcePositiveSl2E,
      modularThetaSourcePositiveScaleField,
      modularThetaSourcePositiveLoweringField,
      modularThetaSourcePositiveVectorField,
      modularThetaSourcePositiveGap] <;>
    ring

/-- Second standard `sl₂` bracket: `[h,f]=-2f`. -/
theorem modularThetaSourcePositive_sl2_bracket_hf :
    modularThetaSourcePositiveVectorFieldBracket
      modularThetaSourcePositiveSl2H modularThetaSourcePositiveSl2F =
      fun i => MvPolynomial.C (-2 : ℂ) * modularThetaSourcePositiveSl2F i := by
  funext i
  cases i <;>
    apply MvPolynomial.funext <;>
    intro v <;>
    simp [modularThetaSourcePositiveVectorFieldBracket,
      modularThetaSourcePositiveSl2H, modularThetaSourcePositiveSl2F,
      modularThetaSourcePositiveScaleField,
      modularThetaSourcePositiveLoweringField] <;>
    ring

/-- Third standard `sl₂` bracket: `[e,f]=h`. -/
theorem modularThetaSourcePositive_sl2_bracket_ef :
    modularThetaSourcePositiveVectorFieldBracket
      modularThetaSourcePositiveSl2E modularThetaSourcePositiveSl2F =
      modularThetaSourcePositiveSl2H := by
  funext i
  cases i <;>
    apply MvPolynomial.funext <;>
    intro v <;>
    simp [modularThetaSourcePositiveVectorFieldBracket,
      modularThetaSourcePositiveSl2H, modularThetaSourcePositiveSl2E,
      modularThetaSourcePositiveSl2F,
      modularThetaSourcePositiveScaleField,
      modularThetaSourcePositiveLoweringField,
      modularThetaSourcePositiveVectorField,
      modularThetaSourcePositiveGap] <;>
    ring

end

end HTGeometry
