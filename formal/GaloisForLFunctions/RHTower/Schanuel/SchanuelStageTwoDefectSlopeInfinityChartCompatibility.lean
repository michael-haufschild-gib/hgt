import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageTwoDefectSlopeProjectiveNormalization

/-!
# Infinity-chart compatibility for the stage-two Schanuel slope point

This file identifies the pullback section map on `D₊(U₁)` with the concrete inclusion of the
inverse-slope coordinate ring into the stage-two value field. The denominator is invertible
because the canonical slope is nonzero.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 2000000

private abbrev uInf (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  stageTwoSlopeProjectiveCoordinateMap x core
    (MvPolynomial.X (some PUnit.unit))

private theorem uInf_isUnit (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsUnit (uInf x core) := by
  unfold uInf
  rw [stageTwoSlopeProjectiveCoordinateMap_X_one]
  exact (isUnit_iff_ne_zero.mpr (stageTwoSlope_ne_zero x core)).map _

private noncomputable def sourceInfinityAwayValueRingEquiv (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Localization.Away (uInf x core) ≃+* stageTwoValueField (x 0) (x 1) :=
  (IsLocalization.atUnit
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
      (Localization.Away (uInf x core))
      (uInf x core) (uInf_isUnit x core)).symm.toRingEquiv.trans
    (commRingCatIsoRingEquiv
      (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))))

@[simp]
private theorem sourceInfinityAwayValueRingEquiv_algebraMap
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (r : Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)) :
    sourceInfinityAwayValueRingEquiv x core
        (algebraMap Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
          (Localization.Away (uInf x core)) r) =
      (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).hom.hom r := by
  let e := IsLocalization.atUnit
    Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
    (Localization.Away (uInf x core)) (uInf x core) (uInf_isUnit x core)
  change (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).hom.hom
    (e.symm (algebraMap
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
      (Localization.Away (uInf x core)) r)) = _
  rw [← e.commutes r, e.symm_apply_apply]
  simp

private def infinityBaseToAway (r : AlgNum) :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit)) :=
  HomogeneousLocalization.Away.mk stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) 0
    (MvPolynomial.C r) (by simp)

private def infinityAffineCoordinate :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit)) :=
  HomogeneousLocalization.Away.mk stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) 1
    (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none)

@[simp]
private theorem swapAway_base (r : AlgNum) :
    pUnitOptionSwapAwayRingEquiv (infinityBaseToAway r) =
      optionHeadBaseToAway (σ := PUnit.{1}) r := by
  change pUnitOptionSwapAwayHom (infinityBaseToAway r) = _
  unfold pUnitOptionSwapAwayHom infinityBaseToAway optionHeadBaseToAway
  unfold HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.val_mk, pUnitOptionSwapGradedHom]

@[simp]
private theorem swapAway_coordinate :
    pUnitOptionSwapAwayRingEquiv infinityAffineCoordinate =
      optionHeadAffineCoordinate (R := AlgNum) PUnit.unit := by
  change pUnitOptionSwapAwayHom infinityAffineCoordinate = _
  unfold pUnitOptionSwapAwayHom infinityAffineCoordinate optionHeadAffineCoordinate
  unfold HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.map_mk]
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.val_mk, pUnitOptionSwapGradedHom]

@[simp]
private theorem infinityPolynomialEquiv_base (r : AlgNum) :
    stageTwoSlopeProjectiveInfinityChartPolynomialEquiv (infinityBaseToAway r) =
      Polynomial.C r := by
  change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (optionHeadAwayToPolynomial (R := AlgNum) (σ := PUnit.{1})
        (pUnitOptionSwapAwayRingEquiv (infinityBaseToAway r))) = _
  rw [swapAway_base, optionHeadAwayToPolynomial_base]
  simp

@[simp]
private theorem infinityPolynomialEquiv_coordinate :
    stageTwoSlopeProjectiveInfinityChartPolynomialEquiv infinityAffineCoordinate =
      Polynomial.X := by
  change MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
      (optionHeadAwayToPolynomial (R := AlgNum) (σ := PUnit.{1})
        (pUnitOptionSwapAwayRingEquiv infinityAffineCoordinate)) = _
  rw [swapAway_coordinate, optionHeadAwayToPolynomial_affineCoordinate]
  simp

@[simp]
private theorem infinityPolynomialEquiv_symm_C (r : AlgNum) :
    stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm (Polynomial.C r) =
      infinityBaseToAway r := by
  apply stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.injective
  simp

@[simp]
private theorem infinityPolynomialEquiv_symm_X :
    stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm Polynomial.X =
      infinityAffineCoordinate := by
  apply stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.injective
  simp

private noncomputable def infinityLocalizationMap (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)) →+* Localization.Away (uInf x core) :=
  (IsLocalization.Away.map
      (Localization.Away
        (MvPolynomial.X (some PUnit.unit) :
          MvPolynomial (Option PUnit.{1}) AlgNum))
      (Localization.Away (uInf x core))
      (stageTwoSlopeProjectiveCoordinateMap x core)
      (MvPolynomial.X (some PUnit.unit) :
        MvPolynomial (Option PUnit.{1}) AlgNum)).comp
    (algebraMap
      (HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)))
      (Localization.Away (MvPolynomial.X (some PUnit.unit))))

@[simp]
private theorem infinityLocalizationMap_apply (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x)
    (z : HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit))) :
    infinityLocalizationMap x core z =
      IsLocalization.Away.map
        (Localization.Away
          (MvPolynomial.X (some PUnit.unit) :
            MvPolynomial (Option PUnit.{1}) AlgNum))
        (Localization.Away (uInf x core))
        (stageTwoSlopeProjectiveCoordinateMap x core)
        (MvPolynomial.X (some PUnit.unit) :
          MvPolynomial (Option PUnit.{1}) AlgNum)
        (HomogeneousLocalization.val z) := rfl

@[simp]
private theorem infinityLocalizationMap_base (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) (r : AlgNum) :
    infinityLocalizationMap x core (infinityBaseToAway r) =
      algebraMap Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
        (Localization.Away (uInf x core))
        ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
          (algebraMap AlgNum (stageTwoValueField (x 0) (x 1)) r)) := by
  have hval :
      HomogeneousLocalization.val (infinityBaseToAway r) =
        algebraMap (MvPolynomial (Option PUnit.{1}) AlgNum)
          (Localization.Away
            (MvPolynomial.X (some PUnit.unit) :
              MvPolynomial (Option PUnit.{1}) AlgNum))
          (MvPolynomial.C r) := by
    change Localization.mk (MvPolynomial.C r) ⟨1, by exact Submonoid.one_mem _⟩ = _
    rw [Localization.mk_eq_mk']
    exact IsLocalization.mk'_one _ _
  rw [infinityLocalizationMap_apply, hval]
  simp only [IsLocalization.Away.map, IsLocalization.map_eq]
  simp [stageTwoSlopeProjectiveCoordinateMap]

@[simp]
private theorem infinityLocalizationMap_coordinate (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    infinityLocalizationMap x core infinityAffineCoordinate =
      algebraMap Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
        (Localization.Away (uInf x core))
        ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
          core.rho⁻¹) := by
  have hval :
      HomogeneousLocalization.val infinityAffineCoordinate =
        Localization.mk (MvPolynomial.X none)
          ⟨MvPolynomial.X (some PUnit.unit) ^ 1, by exact ⟨1, rfl⟩⟩ := by
    simp [infinityAffineCoordinate, HomogeneousLocalization.Away.val_mk]
  rw [infinityLocalizationMap_apply, hval, Localization.mk_eq_mk']
  simp only [IsLocalization.Away.map, IsLocalization.map_mk']
  simp only [map_pow, stageTwoSlopeProjectiveCoordinateMap_X_zero,
    stageTwoSlopeProjectiveCoordinateMap_X_one]
  rw [IsLocalization.mk'_eq_iff_eq_mul]
  simp only [pow_one]
  rw [← map_mul]
  congr 1
  calc
    1 = (Scheme.ΓSpecIso
        (.of (stageTwoValueField (x 0) (x 1)))).inv.hom 1 := by simp
    _ = (Scheme.ΓSpecIso
        (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
          (core.rho⁻¹ * core.rho) := by
      simp [stageTwoSlope_ne_zero x core]
    _ = _ := by rw [map_mul]

@[simp]
private theorem infinityChartRingEquiv_base (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) (r : AlgNum) :
    (stageTwoInverseSlopeCoordinateRing x core).val
        (stageTwoSlopeProjectiveInfinityChartRingEquiv x core
          (infinityBaseToAway r)) =
      algebraMap AlgNum (stageTwoValueField (x 0) (x 1)) r := by
  change (Polynomial.aeval core.rho⁻¹)
      (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv
        (infinityBaseToAway r)) = _
  rw [infinityPolynomialEquiv_base]
  simp

@[simp]
private theorem infinityChartRingEquiv_coordinate (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (stageTwoInverseSlopeCoordinateRing x core).val
        (stageTwoSlopeProjectiveInfinityChartRingEquiv x core
          infinityAffineCoordinate) = core.rho⁻¹ := by
  change (Polynomial.aeval core.rho⁻¹)
      (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv
        infinityAffineCoordinate) = _
  rw [infinityPolynomialEquiv_coordinate]
  simp

private theorem infinityLocalizationMap_to_value (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (sourceInfinityAwayValueRingEquiv x core).toRingHom.comp
        (infinityLocalizationMap x core) =
      (stageTwoInverseSlopeCoordinateRing x core).val.toRingHom.comp
        (stageTwoSlopeProjectiveInfinityChartRingEquiv x core).toRingEquiv.toRingHom := by
  let dehomInv :=
    stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm.toRingHom
  have hcomp :
      ((sourceInfinityAwayValueRingEquiv x core).toRingHom.comp
          (infinityLocalizationMap x core)).comp dehomInv =
        ((stageTwoInverseSlopeCoordinateRing x core).val.toRingHom.comp
          (stageTwoSlopeProjectiveInfinityChartRingEquiv x core).toRingEquiv.toRingHom).comp
            dehomInv := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, dehomInv]
      change sourceInfinityAwayValueRingEquiv x core
          (infinityLocalizationMap x core
            (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm
              (Polynomial.C r))) =
        (stageTwoInverseSlopeCoordinateRing x core).val
          (stageTwoSlopeProjectiveInfinityChartRingEquiv x core
            (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm
              (Polynomial.C r)))
      rw [infinityPolynomialEquiv_symm_C, infinityLocalizationMap_base]
      rw [sourceInfinityAwayValueRingEquiv_algebraMap,
        infinityChartRingEquiv_base]
      simp
    · simp only [RingHom.comp_apply, dehomInv]
      change sourceInfinityAwayValueRingEquiv x core
          (infinityLocalizationMap x core
            (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm
              Polynomial.X)) =
        (stageTwoInverseSlopeCoordinateRing x core).val
          (stageTwoSlopeProjectiveInfinityChartRingEquiv x core
            (stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm
              Polynomial.X))
      rw [infinityPolynomialEquiv_symm_X, infinityLocalizationMap_coordinate]
      rw [sourceInfinityAwayValueRingEquiv_algebraMap,
        infinityChartRingEquiv_coordinate]
      simp
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ :=
    stageTwoSlopeProjectiveInfinityChartPolynomialEquiv.symm.surjective z
  exact RingHom.congr_fun hcomp p

private abbrev XInf (x : Fin 2 → ℂ) :=
  Spec (.of (stageTwoValueField (x 0) (x 1)))

private noncomputable def sourceInfinityChartMap (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    ((XInf x).basicOpen (uInf x core)).toScheme ⟶
      Spec (.of (Localization.Away (uInf x core))) :=
  ((XInf x).isoOfEq ((XInf x).toSpecΓ_preimage_basicOpen (uInf x core))).inv ≫
    (XInf x).toSpecΓ ∣_ PrimeSpectrum.basicOpen (uInf x core) ≫
    (basicOpenIsoSpecAway (uInf x core)).hom

private noncomputable instance sourceInfinityChartMap_isIso (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) : IsIso (sourceInfinityChartMap x core) := by
  unfold sourceInfinityChartMap
  infer_instance

private noncomputable def sourceInfinityChartIso (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    ((XInf x).basicOpen (uInf x core)).toScheme ≅
      Spec (.of (Localization.Away (uInf x core))) :=
  asIso (sourceInfinityChartMap x core)

private noncomputable def schemeIsoAppTopInfinity {Y Z : Scheme} (e : Y ≅ Z) :
    Γ(Z, ⊤) ≅ Γ(Y, ⊤) where
  hom := Scheme.Hom.appTop e.hom
  inv := Scheme.Hom.appTop e.inv
  hom_inv_id := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  inv_hom_id := by
    rw [← Scheme.Hom.comp_appTop]
    simp

private noncomputable def sourceInfinityChartSectionsIso (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Γ(Spec (.of (Localization.Away (uInf x core))), ⊤) ≅
      Γ(((XInf x).basicOpen (uInf x core)).toScheme, ⊤) :=
  schemeIsoAppTopInfinity (sourceInfinityChartIso x core)

private theorem sourceInfinityChartSectionsIso_hom (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Scheme.Hom.appTop (sourceInfinityChartIso x core).hom =
      (sourceInfinityChartSectionsIso x core).hom :=
  rfl

@[reassoc]
private theorem sourceInfinityChartSectionsIso_cancel (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Scheme.Hom.appTop (sourceInfinityChartIso x core).hom ≫
      (sourceInfinityChartSectionsIso x core).symm.hom = 𝟙 _ := by
  rw [sourceInfinityChartSectionsIso_hom]
  exact (sourceInfinityChartSectionsIso x core).hom_inv_id
/-- Pullback sections on `D₊(U₁)`, identified with the value field through the actual projective
localization map. -/
noncomputable def stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Γ(XInf x, stageTwoSlopeGenericMap x core ⁻¹ᵁ
      stageTwoSlopeProjectiveInfinityChart) ≃+* stageTwoValueField (x 0) (x 1) :=
  (commRingCatIsoRingEquiv (
    (XInf x).presheaf.mapIso
      (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
        stageTwoSlopeProjectiveLineGrading
        (stageTwoSlopeProjectiveCoordinateMap x core)
        (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
        (by omega) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))).symm).op ≪≫
    ((XInf x).basicOpen (uInf x core)).topIso.symm ≪≫
    (sourceInfinityChartSectionsIso x core).symm ≪≫
    Scheme.ΓSpecIso (.of (Localization.Away (uInf x core))))).trans
      (sourceInfinityAwayValueRingEquiv x core)

@[simp]
private theorem stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned_apply (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x)
    (z : Γ(XInf x, stageTwoSlopeGenericMap x core ⁻¹ᵁ
      stageTwoSlopeProjectiveInfinityChart)) :
    stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned x core z =
      sourceInfinityAwayValueRingEquiv x core
        (((XInf x).presheaf.mapIso
          (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
            stageTwoSlopeProjectiveLineGrading
            (stageTwoSlopeProjectiveCoordinateMap x core)
            (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
            (by omega) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))).symm).op ≪≫
        ((XInf x).basicOpen (uInf x core)).topIso.symm ≪≫
        (sourceInfinityChartSectionsIso x core).symm ≪≫
        Scheme.ΓSpecIso (.of (Localization.Away (uInf x core)))).hom.hom z) :=
  rfl

@[simp]
private theorem projectiveInfinityChartSectionsRingEquiv_apply
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (z : Γ(stageTwoSlopeProjectiveLine,
      stageTwoSlopeProjectiveInfinityChart)) :
    stageTwoSlopeProjectiveInfinityChartSectionsRingEquiv x core z =
      stageTwoSlopeProjectiveInfinityChartRingEquiv x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X (some PUnit.unit) : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)).inv.hom z) :=
  rfl
@[reassoc]
private theorem targetInfinityChartCancel :
    stageTwoSlopeProjectiveInfinityChart.topIso.inv ≫
        Scheme.Hom.appTop
          (Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
            (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
            (by omega)).inv ≫
        (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
          stageTwoSlopeProjectiveLineGrading (MvPolynomial.X (some PUnit.unit))))).hom =
      (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
        (by omega)).inv := by
  let d := Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)
  let e := Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)
  let gamma := Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
    stageTwoSlopeProjectiveLineGrading (MvPolynomial.X (some PUnit.unit))))
  have hd : Scheme.Hom.appTop d.hom =
      gamma.hom ≫ e.hom ≫ stageTwoSlopeProjectiveInfinityChart.topIso.inv := by
    exact Proj.basicOpenToSpec_app_top stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit))
  have hd' : Scheme.Hom.appTop d.hom =
      (gamma.hom ≫ e.hom) ≫ stageTwoSlopeProjectiveInfinityChart.topIso.inv :=
    hd.trans (Category.assoc _ _ _).symm
  change stageTwoSlopeProjectiveInfinityChart.topIso.inv ≫
      Scheme.Hom.appTop d.inv ≫ gamma.hom = e.inv
  rw [← cancel_epi e.hom]
  rw [← cancel_epi gamma.hom]
  conv_lhs =>
    rw [← Category.assoc gamma.hom e.hom]
    rw [← Category.assoc (gamma.hom ≫ e.hom)
      stageTwoSlopeProjectiveInfinityChart.topIso.inv]
  rw [← hd']
  conv_lhs =>
    rw [← Category.assoc (Scheme.Hom.appTop d.hom)
      (Scheme.Hom.appTop d.inv)]
  rw [← Scheme.Hom.comp_appTop]
  simp

private theorem toInfinityBasicOpen_appTop_aligned (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveInfinityChart.topIso.inv ≫
        Scheme.Hom.appTop
          (Proj.toBasicOpenOfGlobalSections stageTwoSlopeProjectiveLineGrading
            (stageTwoSlopeProjectiveCoordinateMap x core) rfl (by omega)
            (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))) ≫
        ((XInf x).basicOpen (uInf x core)).topIso.hom ≫
        ((XInf x).basicOpen (uInf x core)).topIso.inv ≫
        (sourceInfinityChartSectionsIso x core).symm.hom ≫
        (Scheme.ΓSpecIso (.of (Localization.Away (uInf x core)))).hom =
      (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
          (by omega)).inv ≫
        CommRingCat.ofHom (infinityLocalizationMap x core) := by
  rw [Iso.hom_inv_id_assoc]
  have hto :
      Proj.toBasicOpenOfGlobalSections stageTwoSlopeProjectiveLineGrading
          (stageTwoSlopeProjectiveCoordinateMap x core) rfl (by omega)
          (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) =
        (sourceInfinityChartIso x core).hom ≫
          Spec.map (CommRingCat.ofHom (infinityLocalizationMap x core)) ≫
          (Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
            (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
            (by omega)).inv := by
    rfl
  rw [hto]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [sourceInfinityChartSectionsIso_cancel_assoc x core
    (Scheme.ΓSpecIso (.of (Localization.Away (uInf x core)))).hom]
  have hspec := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (infinityLocalizationMap x core))
  rw [← Iso.eq_comp_inv] at hspec
  rw [hspec]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [targetInfinityChartCancel_assoc]

private theorem genericMap_infinity_app_aligned (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeGenericMap x core).app stageTwoSlopeProjectiveInfinityChart ≫
        (XInf x).presheaf.map
          (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
            stageTwoSlopeProjectiveLineGrading
            (stageTwoSlopeProjectiveCoordinateMap x core)
            (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
            (by omega) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))).symm).op.hom ≫
        ((XInf x).basicOpen (uInf x core)).topIso.inv ≫
        (sourceInfinityChartSectionsIso x core).symm.hom ≫
        (Scheme.ΓSpecIso (.of (Localization.Away (uInf x core)))).hom =
      (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X (some PUnit.unit)) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
          (by omega)).inv ≫
        CommRingCat.ofHom (infinityLocalizationMap x core) := by
  have hpre := Proj.fromOfGlobalSections_preimage_basicOpen
    stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
    (by omega) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
  have hcast := Scheme.Hom.appLE_map
    (stageTwoSlopeGenericMap x core)
    (U := stageTwoSlopeProjectiveInfinityChart)
    (V := stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveInfinityChart)
    (V' := (XInf x).basicOpen (uInf x core))
    (by rfl) ((eqToIso hpre.symm).op.hom)
  rw [Scheme.Hom.appLE_eq_app] at hcast
  have hres := Proj.fromOfGlobalSections_resLE
    stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
    (r := MvPolynomial.X (some PUnit.unit)) (by omega)
    (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))
  have happ := congrArg Scheme.Hom.appTop hres
  simp only [Scheme.Hom.resLE_app_top] at happ
  have happ' := congrArg (fun q =>
    stageTwoSlopeProjectiveInfinityChart.topIso.inv ≫ q ≫
      ((XInf x).basicOpen (uInf x core)).topIso.hom) happ
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at happ'
  rw [← Category.assoc]
  rw [← Category.assoc]
  rw [hcast]
  simp only [stageTwoSlopeGenericMap]
  rw [happ']
  exact toInfinityBasicOpen_appTop_aligned x core
/-- Under the aligned chart identifications, the generic projective section map is exactly the
inclusion of the inverse-slope polynomial coordinate ring into the value field. -/
theorem stageTwoSlopeGenericInfinityChart_app_compatibility (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned x core).toRingHom.comp
        ((stageTwoSlopeGenericMap x core).app
          stageTwoSlopeProjectiveInfinityChart).hom =
      (stageTwoInverseSlopeCoordinateRing x core).val.toRingHom.comp
        (stageTwoSlopeProjectiveInfinityChartSectionsRingEquiv x core).toRingHom := by
  apply RingHom.ext
  intro z
  change stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned x core
      (((stageTwoSlopeGenericMap x core).app
        stageTwoSlopeProjectiveInfinityChart).hom z) =
    (stageTwoInverseSlopeCoordinateRing x core).val
      (stageTwoSlopeProjectiveInfinityChartSectionsRingEquiv x core z)
  rw [stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned_apply,
    projectiveInfinityChartSectionsRingEquiv_apply]
  change sourceInfinityAwayValueRingEquiv x core
      ((Scheme.ΓSpecIso (.of (Localization.Away (uInf x core)))).hom.hom
        ((sourceInfinityChartSectionsIso x core).symm.hom.hom
          (((XInf x).basicOpen (uInf x core)).topIso.inv.hom
            (((XInf x).presheaf.map
              (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
                stageTwoSlopeProjectiveLineGrading
                (stageTwoSlopeProjectiveCoordinateMap x core)
                (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
                (by omega) (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit))).symm).op.hom).hom
              (((stageTwoSlopeGenericMap x core).app
                stageTwoSlopeProjectiveInfinityChart).hom z))))) =
    (stageTwoInverseSlopeCoordinateRing x core).val
      (stageTwoSlopeProjectiveInfinityChartRingEquiv x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X (some PUnit.unit) : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)).inv.hom z))
  have hcat := genericMap_infinity_app_aligned x core
  have hring := congrArg CommRingCat.Hom.hom hcat
  have hz := congrArg (fun q => sourceInfinityAwayValueRingEquiv x core q)
    (RingHom.congr_fun hring z)
  simp only [CategoryTheory.comp_apply] at hz
  have hloc := RingHom.congr_fun (infinityLocalizationMap_to_value x core)
    ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X (some PUnit.unit) : MvPolynomial (Option PUnit.{1}) AlgNum)
      (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)).inv.hom z)
  simp only [RingHom.comp_apply] at hloc
  change sourceInfinityAwayValueRingEquiv x core
      (infinityLocalizationMap x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X (some PUnit.unit) : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)).inv.hom z)) =
    (stageTwoInverseSlopeCoordinateRing x core).val
      (stageTwoSlopeProjectiveInfinityChartRingEquiv x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X (some PUnit.unit) : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum (some PUnit.unit)) (by omega)).inv.hom z)) at hloc
  exact hz.trans hloc


end
end GaloisForLFunctions.RHTower
