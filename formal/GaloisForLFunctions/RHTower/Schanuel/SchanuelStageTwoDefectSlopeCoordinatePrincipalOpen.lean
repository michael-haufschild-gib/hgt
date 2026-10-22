import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageTwoDefectSlopeNormalForm
import GaloisForLFunctions.HTGeometry.ABHN.FractionFieldDenominators

/-!
# A common principal open for the four stage-two coordinates

The concrete stage-two value field is the fraction field of the affine normalization ring.  The
two exponent coordinates and two exponential coordinates therefore admit one common nonzero
denominator in that ring.  Localizing away from this denominator gives a single affine open on
which all four coordinates are honest regular functions.

The map from this principal localization back to the concrete value field is constructed
canonically, and each localized coordinate is proved to map to its literal field element.  No
regularity locus or denominator is supplied as a premise.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-- Index type for the two additive and two multiplicative stage-two coordinates. -/
abbrev StageTwoCoordinateIndex := Fin 2 ⊕ Fin 2

/-- The four literal stage-two coordinates in the concrete value field. -/
def stageTwoSlopeCoordinateFamily
    (x : Fin 2 → ℂ) (j : StageTwoCoordinateIndex) :
    stageTwoValueField (x 0) (x 1) :=
  match j with
  | Sum.inl i => stageTwoExponentIn x i
  | Sum.inr i => stageTwoExponentialIn x i

private theorem exists_stageTwoSlopeCoordinateCommonDenominator
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    ∃ d : stageTwoSlopeAffineNormalizationRing x core, d ≠ 0 ∧
      ∀ j : StageTwoCoordinateIndex,
        ∃ n : stageTwoSlopeAffineNormalizationRing x core,
          algebraMap (stageTwoSlopeAffineNormalizationRing x core)
              (stageTwoValueField (x 0) (x 1)) d * stageTwoSlopeCoordinateFamily x j =
            algebraMap (stageTwoSlopeAffineNormalizationRing x core)
              (stageTwoValueField (x 0) (x 1)) n :=
  ABHN.fintype_exists_commonDenominator
    (stageTwoSlopeAffineNormalizationRing x core)
    (stageTwoValueField (x 0) (x 1)) StageTwoCoordinateIndex
    (stageTwoSlopeCoordinateFamily x)

/-- A common denominator for all four stage-two coordinates in the affine normalization ring. -/
noncomputable def stageTwoSlopeCoordinateCommonDenominator
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeAffineNormalizationRing x core :=
  Classical.choose (exists_stageTwoSlopeCoordinateCommonDenominator x core)

private theorem stageTwoSlopeCoordinateCommonDenominator_spec
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeCoordinateCommonDenominator x core ≠ 0 ∧
      ∀ j : StageTwoCoordinateIndex,
        ∃ n : stageTwoSlopeAffineNormalizationRing x core,
          algebraMap (stageTwoSlopeAffineNormalizationRing x core)
              (stageTwoValueField (x 0) (x 1))
              (stageTwoSlopeCoordinateCommonDenominator x core) *
              stageTwoSlopeCoordinateFamily x j =
            algebraMap (stageTwoSlopeAffineNormalizationRing x core)
              (stageTwoValueField (x 0) (x 1)) n :=
  Classical.choose_spec (exists_stageTwoSlopeCoordinateCommonDenominator x core)

/-- The common coordinate denominator is nonzero. -/
theorem stageTwoSlopeCoordinateCommonDenominator_ne_zero
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeCoordinateCommonDenominator x core ≠ 0 :=
  (stageTwoSlopeCoordinateCommonDenominator_spec x core).1

/-- Numerator of one coordinate against the chosen common denominator. -/
noncomputable def stageTwoSlopeCoordinateNumerator
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (j : StageTwoCoordinateIndex) :
    stageTwoSlopeAffineNormalizationRing x core :=
  Classical.choose ((stageTwoSlopeCoordinateCommonDenominator_spec x core).2 j)

/-- Exact common-denominator identity for every coordinate. -/
theorem stageTwoSlopeCoordinateCommonDenominator_mul
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (j : StageTwoCoordinateIndex) :
    algebraMap (stageTwoSlopeAffineNormalizationRing x core)
        (stageTwoValueField (x 0) (x 1))
        (stageTwoSlopeCoordinateCommonDenominator x core) *
        stageTwoSlopeCoordinateFamily x j =
      algebraMap (stageTwoSlopeAffineNormalizationRing x core)
        (stageTwoValueField (x 0) (x 1))
        (stageTwoSlopeCoordinateNumerator x core j) :=
  Classical.choose_spec ((stageTwoSlopeCoordinateCommonDenominator_spec x core).2 j)

/-- Coordinate ring of the common principal open where all four coordinates are regular. -/
abbrev stageTwoSlopeCoordinatePrincipalOpenRing
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  Localization.Away (stageTwoSlopeCoordinateCommonDenominator x core)

/-- Canonical map from the common coordinate principal open to the concrete value field. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenToValueField
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeCoordinatePrincipalOpenRing x core →ₐ[AlgNum]
      stageTwoValueField (x 0) (x 1) :=
  IsLocalization.Away.liftAlgHom (stageTwoSlopeCoordinateCommonDenominator x core)
    (f := IsScalarTower.toAlgHom AlgNum
      (stageTwoSlopeAffineNormalizationRing x core)
      (stageTwoValueField (x 0) (x 1))) (by
        rw [isUnit_iff_ne_zero]
        intro hzero
        apply stageTwoSlopeCoordinateCommonDenominator_ne_zero x core
        exact IsFractionRing.injective
          (stageTwoSlopeAffineNormalizationRing x core)
          (stageTwoValueField (x 0) (x 1)) hzero)

/-- On the normalization ring, the principal-open map is the canonical fraction-field map. -/
@[simp] theorem stageTwoSlopeCoordinatePrincipalOpenToValueField_algebraMap
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (r : stageTwoSlopeAffineNormalizationRing x core) :
    stageTwoSlopeCoordinatePrincipalOpenToValueField x core
        (algebraMap (stageTwoSlopeAffineNormalizationRing x core)
          (stageTwoSlopeCoordinatePrincipalOpenRing x core) r) =
      algebraMap (stageTwoSlopeAffineNormalizationRing x core)
        (stageTwoValueField (x 0) (x 1)) r := by
  simp [stageTwoSlopeCoordinatePrincipalOpenToValueField,
    IsLocalization.Away.liftAlgHom, IsLocalization.Away.lift_eq]

/-- One coordinate as a regular function on the common principal open. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenElement
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (j : StageTwoCoordinateIndex) :
    stageTwoSlopeCoordinatePrincipalOpenRing x core := by
  let d := stageTwoSlopeCoordinateCommonDenominator x core
  have hd : d ∈ Submonoid.powers d := ⟨1, pow_one d⟩
  exact IsLocalization.mk' (stageTwoSlopeCoordinatePrincipalOpenRing x core)
    (stageTwoSlopeCoordinateNumerator x core j) ⟨d, hd⟩

/-- Every regular coordinate on the principal open maps to its literal element of the stage-two
value field. -/
theorem stageTwoSlopeCoordinatePrincipalOpenToValueField_apply
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (j : StageTwoCoordinateIndex) :
    stageTwoSlopeCoordinatePrincipalOpenToValueField x core
        (stageTwoSlopeCoordinatePrincipalOpenElement x core j) =
      stageTwoSlopeCoordinateFamily x j := by
  let R := stageTwoSlopeAffineNormalizationRing x core
  let S := stageTwoSlopeCoordinatePrincipalOpenRing x core
  let K := stageTwoValueField (x 0) (x 1)
  let d := stageTwoSlopeCoordinateCommonDenominator x core
  let n := stageTwoSlopeCoordinateNumerator x core j
  let φ := stageTwoSlopeCoordinatePrincipalOpenToValueField x core
  have hmk := IsLocalization.mk'_spec S n
    (⟨d, ⟨1, pow_one d⟩⟩ : Submonoid.powers d)
  change stageTwoSlopeCoordinatePrincipalOpenElement x core j *
      algebraMap R S d = algebraMap R S n at hmk
  have hmap := congrArg φ hmk
  rw [map_mul] at hmap
  have hfrac := stageTwoSlopeCoordinateCommonDenominator_mul x core j
  have hdK : algebraMap R K d ≠ 0 := by
    intro hzero
    apply stageTwoSlopeCoordinateCommonDenominator_ne_zero x core
    exact IsFractionRing.injective R K hzero
  apply mul_left_cancel₀ hdK
  calc
    algebraMap R K d * φ (stageTwoSlopeCoordinatePrincipalOpenElement x core j) =
        φ (stageTwoSlopeCoordinatePrincipalOpenElement x core j) * algebraMap R K d :=
      mul_comm _ _
    _ = algebraMap R K n := by
      dsimp only [φ] at hmap ⊢
      rw [stageTwoSlopeCoordinatePrincipalOpenToValueField_algebraMap,
        stageTwoSlopeCoordinatePrincipalOpenToValueField_algebraMap] at hmap
      exact hmap
    _ = algebraMap R K d * stageTwoSlopeCoordinateFamily x j := hfrac.symm

end

end GaloisForLFunctions.RHTower
