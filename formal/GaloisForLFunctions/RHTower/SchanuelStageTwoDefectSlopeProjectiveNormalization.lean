import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeAffineNormality
import GaloisForLFunctions.HTGeometry.JointCriticalityHomogeneous
import GaloisForLFunctions.HTGeometry.MvPolynomialOptionHeadAwayEquiv
import GaloisForLFunctions.HTGeometry.TranscendentalSingletonAdjoin
import GaloisForLFunctions.HTGeometry.CommRingCatIsoRingEquiv
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Stage-two Schanuel defect slope: projective relative normalization

This file constructs the actual projective-line generic map with homogeneous coordinates
`[1 : rho]` and its relative normalization in the concrete stage-two value field.  Thus the
projective compactification is no longer represented only by its affine integral-closure chart:
it is a globally glued scheme over `Proj AlgNum[U₀,U₁]`, with an integral normalization map and a
dense map from `Spec K` factoring the generic projective point.

The relative normalization API supplies integrality, universal closedness, separatedness, and
quasi-compactness over the projective line.  Proving finite type of this normalization map, and
hence properness of the normalized model over `AlgNum`, remains a separate finite-normalization
step; none is assumed here.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry
open scoped IntermediateField.algebraAdjoinAdjoin

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

/-- Standard homogeneous grading on the two-coordinate polynomial ring over the algebraic
numbers. -/
abbrev stageTwoSlopeProjectiveLineGrading :=
  optionHeadGrading (R := AlgNum) (σ := PUnit.{1})

noncomputable instance stageTwoSlopeProjectiveLineGradedAlgebra :
    GradedAlgebra stageTwoSlopeProjectiveLineGrading :=
  MvPolynomial.gradedAlgebra

noncomputable instance stageTwoSlopeProjectiveLineScalarTower :
    IsScalarTower AlgNum (stageTwoSlopeProjectiveLineGrading 0)
      (MvPolynomial (Option PUnit.{1}) AlgNum) :=
  IsScalarTower.of_algebraMap_eq (R := AlgNum)
    (S := stageTwoSlopeProjectiveLineGrading 0)
    (A := MvPolynomial (Option PUnit.{1}) AlgNum) (fun _ => rfl)

noncomputable instance stageTwoSlopeProjectiveLineFiniteType :
    Algebra.FiniteType (stageTwoSlopeProjectiveLineGrading 0)
      (MvPolynomial (Option PUnit.{1}) AlgNum) :=
  Algebra.FiniteType.of_restrictScalars_finiteType AlgNum
    (stageTwoSlopeProjectiveLineGrading 0) (MvPolynomial (Option PUnit.{1}) AlgNum)

/-- Projective line carrying the homogeneous slope point `[1 : rho]`. -/
abbrev stageTwoSlopeProjectiveLine :=
  Proj stageTwoSlopeProjectiveLineGrading

/-- The degree-zero homogeneous coordinate ring is the algebraic-number field. -/
noncomputable def stageTwoSlopeGradeZeroToBase :
    stageTwoSlopeProjectiveLineGrading 0 →+* AlgNum where
  toFun p := MvPolynomial.constantCoeff p.1
  map_one' := by simp
  map_mul' p q := map_mul MvPolynomial.constantCoeff p.1 q.1
  map_zero' := by simp
  map_add' p q := by simp

/-- Constant coefficient is bijective on the degree-zero homogeneous coordinate ring. -/
theorem stageTwoSlopeGradeZeroToBase_bijective :
    Function.Bijective stageTwoSlopeGradeZeroToBase := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    have hp : p.1.IsHomogeneous 0 :=
      (MvPolynomial.mem_homogeneousSubmodule 0 p.1).mp p.2
    have hq : q.1.IsHomogeneous 0 :=
      (MvPolynomial.mem_homogeneousSubmodule 0 q.1).mp q.2
    rw [eq_C_of_isHomogeneous_zero hp, eq_C_of_isHomogeneous_zero hq]
    exact congrArg MvPolynomial.C hpq
  · intro a
    refine ⟨⟨MvPolynomial.C a, ?_⟩, by simp [stageTwoSlopeGradeZeroToBase]⟩
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_C (Option PUnit.{1}) a

/-- Canonical identification of the degree-zero ring of the chosen projective line with
`AlgNum`. -/
noncomputable def stageTwoSlopeGradeZeroRingEquiv :
    stageTwoSlopeProjectiveLineGrading 0 ≃+* AlgNum :=
  RingEquiv.ofBijective stageTwoSlopeGradeZeroToBase
    stageTwoSlopeGradeZeroToBase_bijective

/-- The standard projective line is proper over its degree-zero coefficient ring. -/
theorem stageTwoSlopeProjectiveLine_isProper :
    IsProper (Proj.toSpecZero stageTwoSlopeProjectiveLineGrading) := by
  infer_instance

/-- Standard affine slope chart `D₊(U₀)` on the projective line. -/
abbrev stageTwoSlopeProjectiveAffineChart : stageTwoSlopeProjectiveLine.Opens :=
  Proj.basicOpen stageTwoSlopeProjectiveLineGrading (MvPolynomial.X none)

/-- The standard slope chart is affine. -/
theorem stageTwoSlopeProjectiveAffineChart_isAffine :
    IsAffineOpen stageTwoSlopeProjectiveAffineChart := by
  exact Proj.isAffineOpen_basicOpen stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X none)
    (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)

/-- Scheme chart equivalence with the degree-zero homogeneous localization. -/
noncomputable def stageTwoSlopeProjectiveAffineChartIsoSpec :
    stageTwoSlopeProjectiveAffineChart.toScheme ≅
      Spec (.of (HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X none))) :=
  Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)

/-- The standard projective chart ring is exactly the proved polynomial slope coordinate ring. -/
noncomputable def stageTwoSlopeProjectiveAffineChartRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X none) ≃ₐ[AlgNum] stageTwoSlopeCoordinateRing x core :=
  (optionHeadAwayAlgEquiv (R := AlgNum) (σ := PUnit.{1})).trans
    ((MvPolynomial.uniqueAlgEquiv AlgNum PUnit.{1}).trans
      (stageTwoSlopePolynomialAlgEquiv x core))

/-- Global sections of the standard affine projective chart are the concrete slope coordinate
ring. -/
noncomputable def stageTwoSlopeProjectiveAffineChartSectionsRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Γ(stageTwoSlopeProjectiveLine, stageTwoSlopeProjectiveAffineChart) ≃+*
      stageTwoSlopeCoordinateRing x core :=
  (commRingCatIsoRingEquiv (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
      (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)).symm).trans
    (stageTwoSlopeProjectiveAffineChartRingEquiv x core).toRingEquiv

/-- Standard affine chart `D₊(U₁)` containing the point at infinity of the slope line. -/
abbrev stageTwoSlopeProjectiveInfinityChart : stageTwoSlopeProjectiveLine.Opens :=
  Proj.basicOpen stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X (some PUnit.unit))

/-- The standard chart at infinity is affine. -/
theorem stageTwoSlopeProjectiveInfinityChart_isAffine :
    IsAffineOpen stageTwoSlopeProjectiveInfinityChart := by
  exact Proj.isAffineOpen_basicOpen stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X (some PUnit.unit))
    (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)

/-- Scheme chart equivalence at infinity with its degree-zero homogeneous localization. -/
noncomputable def stageTwoSlopeProjectiveInfinityChartIsoSpec :
    stageTwoSlopeProjectiveInfinityChart.toScheme ≅
      Spec (.of (HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)))) :=
  Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X (some PUnit.unit))
    (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)

/-- The chart at infinity is a polynomial ring, with affine coordinate `U₀ / U₁`. -/
noncomputable def stageTwoSlopeProjectiveInfinityChartPolynomialEquiv :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)) ≃+* Polynomial AlgNum :=
  (pUnitOptionSwapAwayRingEquiv (R := AlgNum)).trans
    ((optionHeadAwayRingEquiv (R := AlgNum) (σ := PUnit.{1})).trans
      (MvPolynomial.uniqueAlgEquiv AlgNum PUnit.{1}).toRingEquiv)

/-- Algebraic-number structure on the infinity chart transported from its polynomial
coordinate. -/
noncomputable instance stageTwoSlopeProjectiveInfinityChartAlgebra :
    Algebra AlgNum
      (HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit))) :=
  ((stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm.toRingHom).comp
    (algebraMap AlgNum (Polynomial AlgNum))).toAlgebra

/-- The infinity chart equivalence preserves algebraic-number constants. -/
noncomputable def stageTwoSlopeProjectiveInfinityChartPolynomialAlgEquiv :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)) ≃ₐ[AlgNum] Polynomial AlgNum where
  __ := stageTwoSlopeProjectiveInfinityChartPolynomialEquiv
  commutes' r := by
    change stageTwoSlopeProjectiveInfinityChartPolynomialEquiv
      (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm
        (algebraMap AlgNum (Polynomial AlgNum) r)) = _
    simp

/-- Polynomial coordinate ring generated by the inverse slope on the infinity chart. -/
abbrev stageTwoInverseSlopeCoordinateRing
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  Algebra.adjoin AlgNum
    ({core.rho⁻¹} : Set (stageTwoValueField (x 0) (x 1)))

/-- Rational function field generated by the inverse slope. -/
abbrev stageTwoInverseSlopeRationalField
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  IntermediateField.adjoin AlgNum
    ({core.rho⁻¹} : Set (stageTwoValueField (x 0) (x 1)))

/-- Inverting the nonzero transcendental coordinate does not change its rational function
field. -/
theorem stageTwoInverseSlopeRationalField_eq
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoInverseSlopeRationalField x core = stageTwoSlopeRationalField x core := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    exact (stageTwoSlopeRationalField x core).inv_mem
      (IntermediateField.subset_adjoin AlgNum ({core.rho} : Set _)
        (Set.mem_singleton core.rho))
  · rw [IntermediateField.adjoin_le_iff]
    rw [Set.singleton_subset_iff]
    simpa using (stageTwoInverseSlopeRationalField x core).inv_mem
      (IntermediateField.subset_adjoin AlgNum ({core.rho⁻¹} : Set _)
        (Set.mem_singleton core.rho⁻¹))

/-- The concrete stage-two value field remains finite over the inverse-slope rational function
field. -/
noncomputable instance stageTwoValueField_finite_over_inverseSlope
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    FiniteDimensional (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) := by
  rw [stageTwoInverseSlopeRationalField_eq x core]
  exact core.finite_over_slope

/-- The nonzero canonical slope has a nonzero inverse. -/
theorem stageTwoSlope_ne_zero
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) : core.rho ≠ 0 := by
  intro hrho
  apply core.rho_transcendental
  rw [hrho]
  exact isAlgebraic_zero

/-- The inverse slope is transcendental over the algebraic numbers. -/
theorem stageTwoInverseSlope_transcendental
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Transcendental AlgNum core.rho⁻¹ := by
  intro hinv
  apply core.rho_transcendental
  have h := hinv.inv
  simpa using h

/-- Polynomial evaluation at the inverse slope is an algebra equivalence onto its coordinate
ring. -/
noncomputable def stageTwoInverseSlopePolynomialAlgEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Polynomial AlgNum ≃ₐ[AlgNum] stageTwoInverseSlopeCoordinateRing x core :=
  transcendentalSingletonAdjoinAlgEquiv core.rho⁻¹
    (stageTwoInverseSlope_transcendental x core)

/-- The inverse-slope polynomial coordinate ring is a principal ideal ring. -/
noncomputable instance stageTwoInverseSlopeCoordinateRing_isPrincipalIdealRing
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsPrincipalIdealRing (stageTwoInverseSlopeCoordinateRing x core) :=
  IsPrincipalIdealRing.of_surjective
    (stageTwoInverseSlopePolynomialAlgEquiv x core).toAlgHom
    (stageTwoInverseSlopePolynomialAlgEquiv x core).surjective

/-- The inverse-slope polynomial coordinate ring is a Dedekind domain. -/
noncomputable instance stageTwoInverseSlopeCoordinateRing_isDedekindDomain
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsDedekindDomain (stageTwoInverseSlopeCoordinateRing x core) := by
  infer_instance

/-- Integral closure of the inverse-slope chart in the concrete stage-two value field. -/
abbrev stageTwoInverseSlopeAffineNormalizationRing
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  integralClosure (stageTwoInverseSlopeCoordinateRing x core)
    (stageTwoValueField (x 0) (x 1))

/-- The inverse-slope affine normalization ring is finite over its polynomial coordinate ring. -/
noncomputable instance stageTwoInverseSlopeAffineNormalizationRing_finite
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Module.Finite (stageTwoInverseSlopeCoordinateRing x core)
      (stageTwoInverseSlopeAffineNormalizationRing x core) := by
  letI algInverseSlopeValue : Algebra (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    (stageTwoInverseSlopeRationalField x core).val.toAlgebra
  letI : IsScalarTower AlgNum (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI towerCoordinateInverseSlopeValue :
      IsScalarTower (stageTwoInverseSlopeCoordinateRing x core)
        (stageTwoInverseSlopeRationalField x core)
        (stageTwoValueField (x 0) (x 1)) :=
    IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalgebraAdjoinAdjoin_1
      AlgNum ({core.rho⁻¹} : Set (stageTwoValueField (x 0) (x 1)))
      (stageTwoValueField (x 0) (x 1))
  letI hfinite : FiniteDimensional (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    stageTwoValueField_finite_over_inverseSlope x core
  letI : Algebra.IsAlgebraic (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    @Algebra.IsAlgebraic.of_finite
      (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) _ _ _ algInverseSlopeValue hfinite
  letI : Algebra.IsSeparable (stageTwoInverseSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) := inferInstance
  letI : IsNoetherian (stageTwoInverseSlopeCoordinateRing x core)
      (stageTwoInverseSlopeAffineNormalizationRing x core) :=
    @IsIntegralClosure.isNoetherian
      (stageTwoInverseSlopeCoordinateRing x core)
      (stageTwoInverseSlopeRationalField x core)
      inferInstance inferInstance inferInstance inferInstance
      (stageTwoValueField (x 0) (x 1))
      inferInstance
      (stageTwoInverseSlopeAffineNormalizationRing x core)
      inferInstance algInverseSlopeValue inferInstance towerCoordinateInverseSlopeValue
      inferInstance inferInstance inferInstance inferInstance hfinite
      inferInstance inferInstance inferInstance inferInstance
  exact ⟨IsNoetherian.noetherian ⊤⟩

/-- The infinity projective chart ring is exactly the polynomial inverse-slope coordinate ring. -/
noncomputable def stageTwoSlopeProjectiveInfinityChartRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)) ≃ₐ[AlgNum]
      stageTwoInverseSlopeCoordinateRing x core :=
  stageTwoSlopeProjectiveInfinityChartPolynomialAlgEquiv.trans
    (stageTwoInverseSlopePolynomialAlgEquiv x core)

/-- Global sections of the projective chart at infinity are the inverse-slope coordinate ring. -/
noncomputable def stageTwoSlopeProjectiveInfinityChartSectionsRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Γ(stageTwoSlopeProjectiveLine, stageTwoSlopeProjectiveInfinityChart) ≃+*
      stageTwoInverseSlopeCoordinateRing x core :=
  (commRingCatIsoRingEquiv (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit) : MvPolynomial (Option PUnit.{1}) AlgNum)
      (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)).symm).trans
    (stageTwoSlopeProjectiveInfinityChartRingEquiv x core).toRingEquiv

/-- The two homogeneous coordinates generate the projective-line algebra over degree zero. -/
theorem stageTwoSlopeProjectiveCoordinates_adjoin :
    Algebra.adjoin (stageTwoSlopeProjectiveLineGrading 0)
      (Set.range fun i : Option PUnit.{1} =>
        (MvPolynomial.X i : MvPolynomial (Option PUnit.{1}) AlgNum)) = ⊤ := by
  rw [← top_le_iff]
  intro p hpTop
  clear hpTop
  have hp : p ∈ Algebra.adjoin AlgNum
      (Set.range fun i : Option PUnit.{1} =>
        (MvPolynomial.X i : MvPolynomial (Option PUnit.{1}) AlgNum)) := by
    rw [MvPolynomial.adjoin_range_X]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp => exact Algebra.subset_adjoin hp
  | algebraMap r =>
      exact algebraMap_mem (R := stageTwoSlopeProjectiveLineGrading 0) _
        (⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Option PUnit.{1}) r⟩ :
          stageTwoSlopeProjectiveLineGrading 0)
  | add x y hx hy hx' hy' => exact add_mem hx' hy'
  | mul x y hx hy hx' hy' => exact mul_mem hx' hy'

/-- The two standard affine charts cover the projective slope line. -/
theorem stageTwoSlopeProjectiveStandardCharts_cover :
    ⨆ i : Option PUnit.{1},
      Proj.basicOpen stageTwoSlopeProjectiveLineGrading (MvPolynomial.X i) = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top' stageTwoSlopeProjectiveLineGrading
    (fun i : Option PUnit.{1} => MvPolynomial.X i)
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X AlgNum i⟩)
    stageTwoSlopeProjectiveCoordinates_adjoin

/-- Homogeneous evaluation at the genuine slope point `[1 : core.rho]`, valued in global
sections of the spectrum of the concrete stage-two value field. -/
noncomputable def stageTwoSlopeProjectiveCoordinateMap
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    MvPolynomial (Option PUnit.{1}) AlgNum →+*
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤) :=
  (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom.comp
    (MvPolynomial.eval₂Hom (algebraMap AlgNum (stageTwoValueField (x 0) (x 1)))
      (fun i => match i with | none => 1 | some _ => core.rho))

@[simp]
theorem stageTwoSlopeProjectiveCoordinateMap_X_zero
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveCoordinateMap x core (MvPolynomial.X none) = 1 := by
  simp [stageTwoSlopeProjectiveCoordinateMap]

@[simp]
theorem stageTwoSlopeProjectiveCoordinateMap_X_one
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveCoordinateMap x core (MvPolynomial.X (some PUnit.unit)) =
      (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom core.rho := by
  simp [stageTwoSlopeProjectiveCoordinateMap]

/-- The homogeneous evaluation sees the irrelevant ideal as the unit ideal, because the first
projective coordinate is `1`. -/
theorem stageTwoSlopeProjectiveCoordinateMap_irrelevant
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Ideal.map (stageTwoSlopeProjectiveCoordinateMap x core)
      (HomogeneousIdeal.irrelevant stageTwoSlopeProjectiveLineGrading).toIdeal = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  rw [← stageTwoSlopeProjectiveCoordinateMap_X_zero x core]
  apply Ideal.mem_map_of_mem
  change MvPolynomial.X none ∈ HomogeneousIdeal.irrelevant stageTwoSlopeProjectiveLineGrading
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
  apply DirectSum.decompose_of_mem_ne stageTwoSlopeProjectiveLineGrading
  · change MvPolynomial.X none ∈
      MvPolynomial.homogeneousSubmodule (Option PUnit.{1}) AlgNum 1
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X AlgNum none
  · omega

/-- Actual generic projective point `[1 : core.rho] : Spec K → P¹_AlgNum`. -/
noncomputable def stageTwoSlopeGenericMap
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Spec (.of (stageTwoValueField (x 0) (x 1))) ⟶ stageTwoSlopeProjectiveLine :=
  Proj.fromOfGlobalSections stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)

/-- The generic slope point lies in the standard affine chart, whose pullback is all of
`Spec K`. -/
theorem stageTwoSlopeGenericMap_preimage_affineChart
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart = ⊤ := by
  change Proj.fromOfGlobalSections stageTwoSlopeProjectiveLineGrading
      (stageTwoSlopeProjectiveCoordinateMap x core)
      (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core) ⁻¹ᵁ
    Proj.basicOpen stageTwoSlopeProjectiveLineGrading (MvPolynomial.X none) = ⊤
  rw [Proj.fromOfGlobalSections_preimage_basicOpen
    stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
    (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)]
  simp

/-- The generic slope point also lies in the infinity chart because `core.rho` is nonzero. -/
theorem stageTwoSlopeGenericMap_preimage_infinityChart
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveInfinityChart = ⊤ := by
  change Proj.fromOfGlobalSections stageTwoSlopeProjectiveLineGrading
      (stageTwoSlopeProjectiveCoordinateMap x core)
      (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core) ⁻¹ᵁ
    Proj.basicOpen stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit)) = ⊤
  rw [Proj.fromOfGlobalSections_preimage_basicOpen
    stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
    (by omega) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))]
  rw [eq_top_iff]
  intro p hp
  rw [stageTwoSlopeProjectiveCoordinateMap_X_one]
  have hUnit : IsUnit
      ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom core.rho) :=
    (isUnit_iff_ne_zero.mpr (stageTwoSlope_ne_zero x core)).map _
  change ∃ hpTop : p ∈ (⊤ : (Spec (.of (stageTwoValueField (x 0) (x 1)))).Opens),
    IsUnit _
  exact ⟨trivial, hUnit.map _⟩

/-- Sections of the generic source over the pullback of the affine chart are the concrete
stage-two value field. -/
noncomputable def stageTwoSlopeGenericAffineChartSectionsRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
      stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart) ≃+*
      stageTwoValueField (x 0) (x 1) := by
  let e : CommRingCat.of
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
        stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart) ≅
      CommRingCat.of (stageTwoValueField (x 0) (x 1)) :=
    (Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.mapIso
        (eqToIso (stageTwoSlopeGenericMap_preimage_affineChart x core).symm).op ≪≫
      Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))
  exact commRingCatIsoRingEquiv e

/-- Sections of the generic source over the pullback of the infinity chart are the concrete
stage-two value field. -/
noncomputable def stageTwoSlopeGenericInfinityChartSectionsRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
      stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveInfinityChart) ≃+*
      stageTwoValueField (x 0) (x 1) := by
  let e : CommRingCat.of
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
        stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveInfinityChart) ≅
      CommRingCat.of (stageTwoValueField (x 0) (x 1)) :=
    (Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.mapIso
        (eqToIso (stageTwoSlopeGenericMap_preimage_infinityChart x core).symm).op ≪≫
      Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))
  exact commRingCatIsoRingEquiv e

/-- Relative normalization of the projective slope line in the concrete stage-two value field. -/
noncomputable abbrev stageTwoSlopeProjectiveNormalization
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  (stageTwoSlopeGenericMap x core).normalization

/-- The projective relative normalization is integral as a scheme. -/
noncomputable instance stageTwoSlopeProjectiveNormalization_isIntegral
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsIntegral (stageTwoSlopeProjectiveNormalization x core) := by
  infer_instance

/-- Integral normalization morphism from the global model to the projective slope line. -/
noncomputable abbrev stageTwoSlopeProjectiveNormalizationToLine
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveNormalization x core ⟶ stageTwoSlopeProjectiveLine :=
  (stageTwoSlopeGenericMap x core).fromNormalization

noncomputable instance stageTwoSlopeProjectiveNormalizationToLine_isIntegral
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsIntegralHom (stageTwoSlopeProjectiveNormalizationToLine x core) := by
  infer_instance

/-- Dense generic-field map into the projective relative normalization. -/
noncomputable abbrev stageTwoSlopeProjectiveGenericInclusion
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Spec (.of (stageTwoValueField (x 0) (x 1))) ⟶
      stageTwoSlopeProjectiveNormalization x core :=
  (stageTwoSlopeGenericMap x core).toNormalization

noncomputable instance stageTwoSlopeProjectiveGenericInclusion_isDominant
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsDominant (stageTwoSlopeProjectiveGenericInclusion x core) := by
  infer_instance

/-- The dense generic-field map followed by normalization is exactly `[1 : core.rho]`. -/
theorem stageTwoSlopeProjectiveNormalization_factorization
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveGenericInclusion x core ≫
      stageTwoSlopeProjectiveNormalizationToLine x core =
        stageTwoSlopeGenericMap x core := by
  exact Scheme.Hom.toNormalization_fromNormalization _

/-- Structural map of the normalized model to the degree-zero coefficient spectrum. -/
noncomputable def stageTwoSlopeProjectiveNormalizationToGradeZero
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveNormalization x core ⟶
      Spec (.of (stageTwoSlopeProjectiveLineGrading 0)) :=
  stageTwoSlopeProjectiveNormalizationToLine x core ≫
    Proj.toSpecZero stageTwoSlopeProjectiveLineGrading

/-- Relative normalization over the projective line is universally closed. -/
noncomputable instance stageTwoSlopeProjectiveNormalization_universallyClosed
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    UniversallyClosed (stageTwoSlopeProjectiveNormalizationToGradeZero x core) := by
  change UniversallyClosed
    ((stageTwoSlopeGenericMap x core).fromNormalization ≫
      Proj.toSpecZero stageTwoSlopeProjectiveLineGrading)
  infer_instance

/-- Relative normalization over the projective line is separated. -/
noncomputable instance stageTwoSlopeProjectiveNormalization_isSeparated
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsSeparated (stageTwoSlopeProjectiveNormalizationToGradeZero x core) := by
  change IsSeparated
    ((stageTwoSlopeGenericMap x core).fromNormalization ≫
      Proj.toSpecZero stageTwoSlopeProjectiveLineGrading)
  infer_instance

/-- Relative normalization over the projective line is quasi-compact. -/
noncomputable instance stageTwoSlopeProjectiveNormalization_quasiCompact
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    QuasiCompact (stageTwoSlopeProjectiveNormalizationToGradeZero x core) := by
  infer_instance

end

end GaloisForLFunctions.RHTower
