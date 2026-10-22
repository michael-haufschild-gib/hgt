import GaloisForLFunctions.RHTower.Suzuki.SuzukiSupportPrunedSelfAdjointSeamCarrier
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Exact exterior Feshbach elimination for Suzuki seam carriers

Support compression is not inverse compression.  This module certifies the exact two-block
elimination law and the positive Gram sign of the exterior-return self-energy.  It also instantiates
the Gram factor with Suzuki's actual coordinate projection and finite prime adjacency.
-/

open Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-- Exterior-return self-energy for a two-block continuous-linear system. -/
def feshbachSelfEnergy
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (B : Y →L[ℂ] X) (R : Y →L[ℂ] Y) (C : X →L[ℂ] Y) :
    X →L[ℂ] X :=
  B ∘L R ∘L C

/-- Exact exterior elimination.  A left inverse for the exterior block is enough: no inverse of
the effective interior block is assumed. -/
theorem feshbach_eliminate_exterior
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (A : X →L[ℂ] X) (B : Y →L[ℂ] X)
    (C : X →L[ℂ] Y) (D R : Y →L[ℂ] Y)
    (x : X) (y f : Y)
    (hRD : R ∘L D = 1)
    (hInterior : A x + B y = 0)
    (hExterior : C x + D y = f) :
    (A - feshbachSelfEnergy B R C) x = -(B (R f)) := by
  have hy : y = R f - R (C x) := by
    have h := congrArg R hExterior
    have hRDy : R (D y) = y := by
      have h' := DFunLike.congr_fun hRD y
      simpa [ContinuousLinearMap.comp_apply] using h'
    rw [map_add, hRDy] at h
    rw [← h]
    abel
  have hzero : A x + B (R f) - B (R (C x)) = 0 := by
    rw [hy, map_sub] at hInterior
    simpa only [sub_eq_add_neg, add_assoc] using hInterior
  calc
    (A - feshbachSelfEnergy B R C) x =
        A x - B (R (C x)) := by
          simp [feshbachSelfEnergy, ContinuousLinearMap.comp_apply]
    _ = (A x + B (R f) - B (R (C x))) - B (R f) := by abel
    _ = 0 - B (R f) := by rw [hzero]
    _ = -(B (R f)) := zero_sub _

/-- Gram-factor form of a positive exterior self-energy. -/
def feshbachGramSelfEnergy
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (K : X →L[ℂ] Y) :
    X →L[ℂ] X :=
  ContinuousLinearMap.adjoint K ∘L K

/-- Exterior return through a positive inverse block subtracts a positive operator from the
interior block. -/
theorem feshbachGramSelfEnergy_isPositive
    {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (K : X →L[ℂ] Y) :
    (feshbachGramSelfEnergy K).IsPositive := by
  simpa only [feshbachGramSelfEnergy] using
    ContinuousLinearMap.isPositive_adjoint_comp_self K

/-- Strict-interior coordinate projection on the oriented Suzuki seam carrier. -/
def suzukiSeamInteriorProjection (a : ℝ) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  lpCoordinateProjection (suzukiAdmissibleSeamVertices a)

/-- Complementary exterior coordinate projection. -/
def suzukiSeamExteriorProjection (a : ℝ) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  1 - suzukiSeamInteriorProjection a

/-- Actual one-step transition from Suzuki's strict-interior sector to its exterior sector. -/
def suzukiInteriorToExteriorPrimeTransition
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  suzukiSeamExteriorProjection a ∘L
    suzukiFinitePrimeAdjacency steps weight s ∘L
      suzukiSeamInteriorProjection a

/-- Suzuki exterior-return Gram correction.  `Droot` is the square-root factor of the positive
exterior inverse; the projection and adjacency are the literal seam operators. -/
def suzukiExteriorReturnGramSelfEnergy
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι)
    (Droot : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  feshbachGramSelfEnergy
    (Droot ∘L suzukiInteriorToExteriorPrimeTransition a steps weight s)

/-- The exact Suzuki exterior-return Gram correction is positive for every square-root exterior
factor. -/
theorem suzukiExteriorReturnGramSelfEnergy_isPositive
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι)
    (Droot : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) :
    (suzukiExteriorReturnGramSelfEnergy a steps weight s Droot).IsPositive := by
  exact feshbachGramSelfEnergy_isPositive
    (Droot ∘L suzukiInteriorToExteriorPrimeTransition a steps weight s)

end GaloisForLFunctions.RHTower
