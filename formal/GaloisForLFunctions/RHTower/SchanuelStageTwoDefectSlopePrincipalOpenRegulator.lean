import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopePrincipalOpenComplexPoints
import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeNormalForm

/-!
# Smooth-path regulator on the common stage-two principal open

A smooth path here is a path through the actual relative complex-point space of the common
coordinate principal open whose evaluation against every regular function is smooth.  Its source
is the complexification of an `AlgNum`-valued point and its target is the canonical point carrying
the literal tuple `(x₁,x₂,exp x₁,exp x₂)`.

All derivative fields required by the regulator theorem are derived from affine smoothness.  The
algebraic endpoint values are derived from source factorization, and terminal values are derived
from the canonical target computation.  Only divisor avoidance and the path's original endpoints
remain as the quantified geometric conditions from the paper statement.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry Set

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-- Complexification of an `AlgNum`-valued point of the common coordinate principal open. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenBaseComplexPoint
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    (q : stageTwoSlopeCoordinatePrincipalOpenRing x core →ₐ[AlgNum] AlgNum) :
    RelativeAlgSpec AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core) where
  toRingHom := (algebraMap AlgNum ℂ).comp q.toRingHom
  commutes' c := by simp

/-- A genuinely smooth path in the relative complex-point space of the common coordinate
principal open, from an algebraic point to the canonical exponential target. -/
structure StageTwoCoordinatePrincipalOpenSmoothPath
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (a b : ℝ) where
  point : ℝ → RelativeAlgSpec AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core)
  smooth : RelativeAlgSpec.IsSmoothPath AlgNum
    (stageTwoSlopeCoordinatePrincipalOpenRing x core) point
  basePoint : stageTwoSlopeCoordinatePrincipalOpenRing x core →ₐ[AlgNum] AlgNum
  parameter_order : a ≤ b
  source : point a = stageTwoSlopeCoordinatePrincipalOpenBaseComplexPoint basePoint
  target : point b = stageTwoSlopeCoordinatePrincipalOpenTargetPoint x core
  avoids_multiplicative_divisor : ∀ i t, t ∈ Icc a b →
    stageTwoSlopeCoordinatePrincipalOpenValue x core (point t) (Sum.inr i) ≠ 0

/-- Forget an affine smooth path to its four literal coordinate pullbacks.  Differentiability,
continuous derivatives, algebraic source values, and target values are all derived. -/
noncomputable def StageTwoCoordinatePrincipalOpenSmoothPath.toCoordinatePath
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoCoordinatePrincipalOpenSmoothPath x core a b) :
    StageTwoDivisorAvoidingCoordinatePath x a b where
  X i t := stageTwoSlopeCoordinatePrincipalOpenValue x core (path.point t) (Sum.inl i)
  Y i t := stageTwoSlopeCoordinatePrincipalOpenValue x core (path.point t) (Sum.inr i)
  X' i := deriv fun t =>
    stageTwoSlopeCoordinatePrincipalOpenValue x core (path.point t) (Sum.inl i)
  Y' i := deriv fun t =>
    stageTwoSlopeCoordinatePrincipalOpenValue x core (path.point t) (Sum.inr i)
  parameter_order := path.parameter_order
  hasDeriv_X i t _ := by
    exact (((GaloisForLFunctions.RHTower.RelativeAlgSpec.IsSmoothPath.contDiff_stageTwoSlopeCoordinatePrincipalOpenValue
      path.smooth (Sum.inl i))).differentiable (by simp) t).hasDerivAt
  hasDeriv_Y i t _ := by
    exact (((GaloisForLFunctions.RHTower.RelativeAlgSpec.IsSmoothPath.contDiff_stageTwoSlopeCoordinatePrincipalOpenValue
      path.smooth (Sum.inr i))).differentiable (by simp) t).hasDerivAt
  continuous_X' i := by
    exact ((GaloisForLFunctions.RHTower.RelativeAlgSpec.IsSmoothPath.contDiff_stageTwoSlopeCoordinatePrincipalOpenValue
      path.smooth (Sum.inl i)).continuous_deriv (by simp)).continuousOn
  continuous_Y' i := by
    exact ((GaloisForLFunctions.RHTower.RelativeAlgSpec.IsSmoothPath.contDiff_stageTwoSlopeCoordinatePrincipalOpenValue
      path.smooth (Sum.inr i)).continuous_deriv (by simp)).continuousOn
  avoids_multiplicative_divisor := path.avoids_multiplicative_divisor
  algebraic_base_X i := by
    rw [path.source]
    change ((path.basePoint
      (stageTwoSlopeCoordinatePrincipalOpenElement x core (Sum.inl i)) : AlgNum) : ℂ) ∈ AlgNum
    exact (path.basePoint
      (stageTwoSlopeCoordinatePrincipalOpenElement x core (Sum.inl i))).property
  algebraic_base_Y i := by
    rw [path.source]
    change ((path.basePoint
      (stageTwoSlopeCoordinatePrincipalOpenElement x core (Sum.inr i)) : AlgNum) : ℂ) ∈ AlgNum
    exact (path.basePoint
      (stageTwoSlopeCoordinatePrincipalOpenElement x core (Sum.inr i))).property
  terminal_X i := by
    rw [path.target]
    exact stageTwoSlopeCoordinatePrincipalOpenTargetPoint_exponentValue x core i
  terminal_Y i := by
    rw [path.target]
    exact stageTwoSlopeCoordinatePrincipalOpenTargetPoint_exponentialValue x core i

/-- Exact simultaneous regulator identities for every smooth divisor-avoiding path in the common
coordinate principal open from an algebraic point to the canonical exponential target. -/
theorem exists_stageTwoCoordinatePrincipalOpenPathRegulatorWitness
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoCoordinatePrincipalOpenSmoothPath x core a b) :
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath) :=
  exists_stageTwoRegulatorWitness path.toCoordinatePath

end

end GaloisForLFunctions.RHTower
