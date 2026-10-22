import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageTwoDefectSlopeProjectiveRegulator

/-!
# Generic complex target point on the stage-two projective normalization

The concrete stage-two value field is an intermediate field of `ℂ`.  Its literal inclusion into
`ℂ`, followed contravariantly by `Spec` and then by the dense generic inclusion into the
projective normalization, produces a canonical complex-valued point.  This file proves that the
point lies over the standard algebraic-number embedding, is centered at the generic point, and is
regular for all four stage-two coordinate rational functions.  Function-field pullback coherence
then identifies their evaluated values with the literal generators `xᵢ` and `exp xᵢ`.

This is the algebraic target endpoint required by the projective regulator construction.  No
analytic path to this endpoint is asserted here.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry TopologicalSpace

noncomputable section

/-- Literal inclusion of the concrete stage-two value field into `ℂ`. -/
noncomputable def stageTwoValueFieldComplexInclusionRingHom (x : Fin 2 → ℂ) :
    stageTwoValueField (x 0) (x 1) →+* ℂ :=
  (stageTwoValueField (x 0) (x 1)).val.toRingHom

/-- Complex point obtained from the concrete value-field inclusion and the normalized generic
inclusion. -/
noncomputable def stageTwoSlopeProjectiveGenericComplexPoint
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeProjectiveModel x core).ComplexPoint :=
  Spec.map (CommRingCat.ofHom (stageTwoValueFieldComplexInclusionRingHom x)) ≫
    stageTwoSlopeProjectiveGenericInclusion x core

noncomputable instance stageTwoValueFieldComplexSpecMap_isDominant
    (x : Fin 2 → ℂ) :
    IsDominant (Spec.map
      (CommRingCat.ofHom (stageTwoValueFieldComplexInclusionRingHom x))) := by
  infer_instance

noncomputable instance stageTwoSlopeProjectiveGenericComplexPoint_isDominant
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsDominant (stageTwoSlopeProjectiveGenericComplexPoint x core) := by
  dsimp [stageTwoSlopeProjectiveGenericComplexPoint]
  infer_instance

/-- The canonical complex point is centered at the generic point of the normalization. -/
theorem stageTwoSlopeProjectiveGenericComplexPoint_center
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeProjectiveGenericComplexPoint x core).center =
      genericPoint (stageTwoSlopeProjectiveModel x core) := by
  exact (stageTwoSlopeProjectiveGenericComplexPoint x core).map_genericPoint_of_isDominant

/-- The canonical complex point lies over the standard embedding of algebraic numbers in `ℂ`. -/
theorem stageTwoSlopeProjectiveGenericComplexPoint_over
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveGenericComplexPoint x core ≫
        stageTwoSlopeProjectiveNormalizationToAlgNum x core =
      Spec.map (CommRingCat.ofHom (algebraMap AlgNum ℂ)) := by
  dsimp [stageTwoSlopeProjectiveGenericComplexPoint,
    stageTwoSlopeProjectiveNormalizationToAlgNum,
    stageTwoSlopeProjectiveNormalizationToGradeZero]
  simp only [Category.assoc]
  rw [← Category.assoc (stageTwoSlopeProjectiveGenericInclusion x core)
    (stageTwoSlopeProjectiveNormalizationToLine x core)
    (Proj.toSpecZero stageTwoSlopeProjectiveLineGrading ≫
      stageTwoSlopeGradeZeroSpecIso.hom)]
  rw [stageTwoSlopeProjectiveNormalization_factorization]
  rw [← Category.assoc (stageTwoSlopeGenericMap x core)
    (Proj.toSpecZero stageTwoSlopeProjectiveLineGrading)
    stageTwoSlopeGradeZeroSpecIso.hom]
  unfold stageTwoSlopeGenericMap
  rw [Proj.fromOfGlobalSections_toSpecZero]
  simp only [Category.assoc]
  rw [Scheme.toSpecΓ_eq_specMap_ΓSpecIso_hom]
  unfold stageTwoSlopeGradeZeroSpecIso
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  change stageTwoValueFieldComplexInclusionRingHom x
      ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).hom
        (stageTwoSlopeProjectiveCoordinateMap x core
          (algebraMap (stageTwoSlopeProjectiveLineGrading 0)
            (MvPolynomial (Option PUnit.{1}) AlgNum)
            (stageTwoSlopeGradeZeroRingEquiv.symm r)))) =
    algebraMap AlgNum ℂ r
  have hgrade : stageTwoSlopeGradeZeroRingEquiv.symm r =
      (⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Option PUnit.{1}) r⟩ :
        stageTwoSlopeProjectiveLineGrading 0) := by
    apply stageTwoSlopeGradeZeroRingEquiv.injective
    simp [stageTwoSlopeGradeZeroRingEquiv, stageTwoSlopeGradeZeroToBase]
  rw [hgrade]
  simp [stageTwoValueFieldComplexInclusionRingHom,
    stageTwoSlopeProjectiveCoordinateMap]

/-- Canonical generic complex point, packaged over `Spec AlgNum`. -/
noncomputable def stageTwoSlopeProjectiveGenericComplexPointOver
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeProjectiveModel x core).ComplexPointOver AlgNum
      (stageTwoSlopeProjectiveNormalizationToAlgNum x core) where
  hom := stageTwoSlopeProjectiveGenericComplexPoint x core
  commutes := stageTwoSlopeProjectiveGenericComplexPoint_over x core

/-- The canonical generic complex point is regular for all four stage-two coordinates. -/
noncomputable def stageTwoProjectiveGenericCoordinatePoint
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    StageTwoProjectiveCoordinatePoint x core where
  point := stageTwoSlopeProjectiveGenericComplexPointOver x core
  exponentRegular := fun i =>
    Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint
      (stageTwoSlopeProjectiveGenericComplexPoint x core)
      (stageTwoSlopeProjectiveGenericComplexPoint_center x core)
      (stageTwoSlopeProjectiveExponentCoordinate x core i)
  exponentialRegular := fun i =>
    Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint
      (stageTwoSlopeProjectiveGenericComplexPoint x core)
      (stageTwoSlopeProjectiveGenericComplexPoint_center x core)
      (stageTwoSlopeProjectiveExponentialCoordinate x core i)

/-- Each additive coordinate at the canonical generic complex point is the literal source value
`xᵢ`. -/
theorem stageTwoProjectiveGenericCoordinatePoint_exponentValue
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (i : Fin 2) :
    (stageTwoProjectiveGenericCoordinatePoint x core).exponentValue i = x i := by
  unfold StageTwoProjectiveCoordinatePoint.exponentValue
  unfold stageTwoProjectiveGenericCoordinatePoint
  change (Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint
    (stageTwoSlopeProjectiveGenericComplexPoint x core)
    (stageTwoSlopeProjectiveGenericComplexPoint_center x core)
    (stageTwoSlopeProjectiveExponentCoordinate x core i)).value = x i
  rw [Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint_value]
  unfold stageTwoSlopeProjectiveExponentCoordinate
  unfold stageTwoSlopeProjectiveGenericComplexPoint
  rw [Scheme.Hom.functionFieldPullback_comp]
  simp only [CommRingCat.comp_apply]
  rw [show (stageTwoSlopeProjectiveGenericInclusion x core).functionFieldPullback
      (stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
        (stageTwoExponentIn x i)) =
      Scheme.specFunctionFieldAlgEquiv
        (stageTwoValueField (x 0) (x 1)) (stageTwoExponentIn x i) by
    exact RingHom.congr_fun
      (stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv_pullback x core)
      (stageTwoExponentIn x i)]
  rw [Scheme.specMap_functionFieldPullback_specFunctionFieldAlgEquiv]
  rw [Scheme.specFieldStalkEquiv_symm_specFunctionFieldAlgEquiv]
  rfl

/-- Each multiplicative coordinate at the canonical generic complex point is the literal source
value `exp xᵢ`. -/
theorem stageTwoProjectiveGenericCoordinatePoint_exponentialValue
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (i : Fin 2) :
    (stageTwoProjectiveGenericCoordinatePoint x core).exponentialValue i =
      Complex.exp (x i) := by
  unfold StageTwoProjectiveCoordinatePoint.exponentialValue
  unfold stageTwoProjectiveGenericCoordinatePoint
  change (Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint
    (stageTwoSlopeProjectiveGenericComplexPoint x core)
    (stageTwoSlopeProjectiveGenericComplexPoint_center x core)
    (stageTwoSlopeProjectiveExponentialCoordinate x core i)).value = Complex.exp (x i)
  rw [Scheme.rationalFunctionRegularAtComplexPoint_of_center_eq_genericPoint_value]
  unfold stageTwoSlopeProjectiveExponentialCoordinate
  unfold stageTwoSlopeProjectiveGenericComplexPoint
  rw [Scheme.Hom.functionFieldPullback_comp]
  simp only [CommRingCat.comp_apply]
  rw [show (stageTwoSlopeProjectiveGenericInclusion x core).functionFieldPullback
      (stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
        (stageTwoExponentialIn x i)) =
      Scheme.specFunctionFieldAlgEquiv
        (stageTwoValueField (x 0) (x 1)) (stageTwoExponentialIn x i) by
    exact RingHom.congr_fun
      (stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv_pullback x core)
      (stageTwoExponentialIn x i)]
  rw [Scheme.specMap_functionFieldPullback_specFunctionFieldAlgEquiv]
  rw [Scheme.specFieldStalkEquiv_symm_specFunctionFieldAlgEquiv]
  rfl

end

end GaloisForLFunctions.RHTower
