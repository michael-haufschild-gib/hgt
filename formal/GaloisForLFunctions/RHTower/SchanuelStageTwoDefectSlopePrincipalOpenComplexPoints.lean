import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeCoordinatePrincipalOpen
import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeGenericTargetPoint
import GaloisForLFunctions.HTGeometry.AlgebraSpectrumSmoothPath

/-!
# Complex points of the stage-two coordinate principal open

The common coordinate principal open has a canonical complex point induced by the literal
embedding of the stage-two value field in `ℂ`.  Every one of its four regular coordinate values is
proved to be the corresponding `xᵢ` or `exp xᵢ`.

The presentation-independent affine smooth-path structure from `AlgebraSpectrumSmoothPath` makes
every regular coordinate evaluation smooth automatically.  This supplies the exact analytic
structure on the common affine open; no coordinatewise differentiability premise is added.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 1000000

/-- Canonical complex point of the common coordinate principal open obtained from the literal
stage-two value-field embedding. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenTargetPoint
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    RelativeAlgSpec AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core) where
  toRingHom := (stageTwoValueFieldComplexInclusionRingHom x).comp
    (stageTwoSlopeCoordinatePrincipalOpenToValueField x core).toRingHom
  commutes' c := by
    change stageTwoValueFieldComplexInclusionRingHom x
        (stageTwoSlopeCoordinatePrincipalOpenToValueField x core
          (algebraMap AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core) c)) =
      algebraMap AlgNum ℂ c
    rw [(stageTwoSlopeCoordinatePrincipalOpenToValueField x core).commutes c]
    rfl

/-- Value of one regular coordinate at a relative complex point of the common principal open. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenValue
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (p : RelativeAlgSpec AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core))
    (j : StageTwoCoordinateIndex) : ℂ :=
  p (stageTwoSlopeCoordinatePrincipalOpenElement x core j)

/-- The canonical target point evaluates every regular coordinate to its literal value-field
element. -/
theorem stageTwoSlopeCoordinatePrincipalOpenTargetPoint_value
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (j : StageTwoCoordinateIndex) :
    stageTwoSlopeCoordinatePrincipalOpenValue x core
        (stageTwoSlopeCoordinatePrincipalOpenTargetPoint x core) j =
      (stageTwoSlopeCoordinateFamily x j : ℂ) := by
  unfold stageTwoSlopeCoordinatePrincipalOpenValue
  unfold stageTwoSlopeCoordinatePrincipalOpenTargetPoint
  change stageTwoValueFieldComplexInclusionRingHom x
      (stageTwoSlopeCoordinatePrincipalOpenToValueField x core
        (stageTwoSlopeCoordinatePrincipalOpenElement x core j)) = _
  rw [stageTwoSlopeCoordinatePrincipalOpenToValueField_apply]
  rfl

/-- The additive values of the canonical principal-open target are the literal exponents. -/
theorem stageTwoSlopeCoordinatePrincipalOpenTargetPoint_exponentValue
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (i : Fin 2) :
    stageTwoSlopeCoordinatePrincipalOpenValue x core
        (stageTwoSlopeCoordinatePrincipalOpenTargetPoint x core) (Sum.inl i) = x i := by
  rw [stageTwoSlopeCoordinatePrincipalOpenTargetPoint_value]
  rfl

/-- The multiplicative values of the canonical principal-open target are the literal
exponentials. -/
theorem stageTwoSlopeCoordinatePrincipalOpenTargetPoint_exponentialValue
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (i : Fin 2) :
    stageTwoSlopeCoordinatePrincipalOpenValue x core
        (stageTwoSlopeCoordinatePrincipalOpenTargetPoint x core) (Sum.inr i) =
      Complex.exp (x i) := by
  rw [stageTwoSlopeCoordinatePrincipalOpenTargetPoint_value]
  rfl

/-- Every regular stage-two coordinate evaluates smoothly along every smooth path in the common
principal open. -/
theorem RelativeAlgSpec.IsSmoothPath.contDiff_stageTwoSlopeCoordinatePrincipalOpenValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    {γ : ℝ → RelativeAlgSpec AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core)}
    (hγ : RelativeAlgSpec.IsSmoothPath AlgNum
      (stageTwoSlopeCoordinatePrincipalOpenRing x core) γ)
    (j : StageTwoCoordinateIndex) :
    ContDiff ℝ ⊤ fun t => stageTwoSlopeCoordinatePrincipalOpenValue x core (γ t) j :=
  hγ (stageTwoSlopeCoordinatePrincipalOpenElement x core j)

end

end GaloisForLFunctions.RHTower
