import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeProjectiveNormalization

/-!
# Affine-chart compatibility for the stage-two Schanuel slope point

This file identifies the pullback section map on `D₊(U₀)` with the concrete inclusion of the
slope coordinate ring into the stage-two value field. The proof follows the actual projective
localization map; it does not replace the pullback sections by an unrelated abstract copy.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000

private abbrev K (x : Fin 2 → ℂ) := stageTwoValueField (x 0) (x 1)

private abbrev X (x : Fin 2 → ℂ) := Spec (.of (K x))

private abbrev u (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  stageTwoSlopeProjectiveCoordinateMap x core (MvPolynomial.X none)

private noncomputable def sourceChartMap (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    ((X x).basicOpen (u x core)).toScheme ⟶
      Spec (.of (Localization.Away (u x core))) :=
  ((X x).isoOfEq ((X x).toSpecΓ_preimage_basicOpen (u x core))).inv ≫
    (X x).toSpecΓ ∣_ PrimeSpectrum.basicOpen (u x core) ≫
    (basicOpenIsoSpecAway (u x core)).hom

private noncomputable instance sourceChartMap_isIso (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) : IsIso (sourceChartMap x core) := by
  unfold sourceChartMap
  infer_instance

private noncomputable def sourceChartIso (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    ((X x).basicOpen (u x core)).toScheme ≅
      Spec (.of (Localization.Away (u x core))) :=
  asIso (sourceChartMap x core)

private theorem u_isUnit (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsUnit (u x core) := by
  unfold u
  rw [stageTwoSlopeProjectiveCoordinateMap_X_zero]
  exact isUnit_one

private noncomputable def schemeIsoAppTop {Y Z : Scheme} (e : Y ≅ Z) :
    Γ(Z, ⊤) ≅ Γ(Y, ⊤) where
  hom := Scheme.Hom.appTop e.hom
  inv := Scheme.Hom.appTop e.inv
  hom_inv_id := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  inv_hom_id := by
    rw [← Scheme.Hom.comp_appTop]
    simp

private noncomputable def sourceChartSectionsIso (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Γ(Spec (.of (Localization.Away (u x core))), ⊤) ≅
      Γ(((X x).basicOpen (u x core)).toScheme, ⊤) :=
  schemeIsoAppTop (sourceChartIso x core)

private theorem sourceChartSectionsIso_hom (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Scheme.Hom.appTop (sourceChartIso x core).hom =
      (sourceChartSectionsIso x core).hom :=
  rfl

@[reassoc]
private theorem sourceChartSectionsIso_cancel (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Scheme.Hom.appTop (sourceChartIso x core).hom ≫
      (sourceChartSectionsIso x core).symm.hom = 𝟙 _ := by
  rw [sourceChartSectionsIso_hom]
  exact (sourceChartSectionsIso x core).hom_inv_id

private noncomputable def sourceAwayValueRingEquiv (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Localization.Away (u x core) ≃+* stageTwoValueField (x 0) (x 1) :=
  (IsLocalization.atUnit
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
      (Localization.Away (u x core))
      (u x core) (u_isUnit x core)).symm.toRingEquiv.trans
    (commRingCatIsoRingEquiv
      (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))))

@[simp]
private theorem sourceAwayValueRingEquiv_algebraMap (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x)
    (r : Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)) :
    sourceAwayValueRingEquiv x core
        (algebraMap Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
          (Localization.Away (u x core)) r) =
      (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).hom.hom r := by
  let e := IsLocalization.atUnit
    Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
    (Localization.Away (u x core)) (u x core) (u_isUnit x core)
  change (Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).hom.hom
    (e.symm (algebraMap
      Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
      (Localization.Away (u x core)) r)) = _
  rw [← e.commutes r, e.symm_apply_apply]
  simp

/-- Pullback sections on `D₊(U₀)`, identified with the value field through the actual projective
localization map. -/
noncomputable def stageTwoSlopeGenericAffineChartSectionsRingEquivAligned (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    Γ(X x, stageTwoSlopeGenericMap x core ⁻¹ᵁ
      stageTwoSlopeProjectiveAffineChart) ≃+* K x :=
  (commRingCatIsoRingEquiv (
    (X x).presheaf.mapIso
      (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
        stageTwoSlopeProjectiveLineGrading
        (stageTwoSlopeProjectiveCoordinateMap x core)
        (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
        (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)).symm).op ≪≫
    ((X x).basicOpen (u x core)).topIso.symm ≪≫
    (sourceChartSectionsIso x core).symm ≪≫
    Scheme.ΓSpecIso (.of (Localization.Away (u x core))))).trans
      (sourceAwayValueRingEquiv x core)

@[simp]
private theorem stageTwoSlopeGenericAffineChartSectionsRingEquivAligned_apply (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x)
    (z : Γ(X x, stageTwoSlopeGenericMap x core ⁻¹ᵁ
      stageTwoSlopeProjectiveAffineChart)) :
    stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core z =
      sourceAwayValueRingEquiv x core
        (((X x).presheaf.mapIso
          (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
            stageTwoSlopeProjectiveLineGrading
            (stageTwoSlopeProjectiveCoordinateMap x core)
            (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
            (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)).symm).op ≪≫
        ((X x).basicOpen (u x core)).topIso.symm ≪≫
        (sourceChartSectionsIso x core).symm ≪≫
        Scheme.ΓSpecIso (.of (Localization.Away (u x core)))).hom.hom z) :=
  rfl

@[simp]
private theorem projectiveAffineChartSectionsRingEquiv_apply
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (z : Γ(stageTwoSlopeProjectiveLine,
      stageTwoSlopeProjectiveAffineChart)) :
    stageTwoSlopeProjectiveAffineChartSectionsRingEquiv x core z =
      stageTwoSlopeProjectiveAffineChartRingEquiv x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)).inv.hom z) :=
  rfl

private noncomputable def affineLocalizationMap (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X none) →+* Localization.Away (u x core) :=
  (IsLocalization.Away.map
      (Localization.Away
        (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum))
      (Localization.Away (u x core))
      (stageTwoSlopeProjectiveCoordinateMap x core)
      (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)).comp
    (algebraMap (HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X none)) (Localization.Away (MvPolynomial.X none)))

@[simp]
private theorem affineLocalizationMap_apply (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x)
    (z : HomogeneousLocalization.Away stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X none)) :
    affineLocalizationMap x core z =
      IsLocalization.Away.map
        (Localization.Away
          (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum))
        (Localization.Away (u x core))
        (stageTwoSlopeProjectiveCoordinateMap x core)
        (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
        (HomogeneousLocalization.val z) :=
  rfl

@[reassoc]
private theorem targetChartCancel :
    stageTwoSlopeProjectiveAffineChart.topIso.inv ≫
        Scheme.Hom.appTop
          (Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
            (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none)
            (by omega)).inv ≫
        (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
          stageTwoSlopeProjectiveLineGrading (MvPolynomial.X none)))).hom =
      (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
        (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none)
        (by omega)).inv := by
  let d := Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)
  let e := Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
    (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)
  let gamma := Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
    stageTwoSlopeProjectiveLineGrading (MvPolynomial.X none)))
  have hd : Scheme.Hom.appTop d.hom =
      gamma.hom ≫ e.hom ≫ stageTwoSlopeProjectiveAffineChart.topIso.inv := by
    exact Proj.basicOpenToSpec_app_top stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X none)
  have hd' : Scheme.Hom.appTop d.hom =
      (gamma.hom ≫ e.hom) ≫ stageTwoSlopeProjectiveAffineChart.topIso.inv :=
    hd.trans (Category.assoc _ _ _).symm
  change stageTwoSlopeProjectiveAffineChart.topIso.inv ≫
      Scheme.Hom.appTop d.inv ≫ gamma.hom = e.inv
  rw [← cancel_epi e.hom]
  rw [← cancel_epi gamma.hom]
  conv_lhs =>
    rw [← Category.assoc gamma.hom e.hom]
    rw [← Category.assoc (gamma.hom ≫ e.hom)
      stageTwoSlopeProjectiveAffineChart.topIso.inv]
  rw [← hd']
  conv_lhs =>
    rw [← Category.assoc (Scheme.Hom.appTop d.hom)
      (Scheme.Hom.appTop d.inv)]
  rw [← Scheme.Hom.comp_appTop]
  simp

private theorem toBasicOpen_appTop_aligned (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveAffineChart.topIso.inv ≫
        Scheme.Hom.appTop
          (Proj.toBasicOpenOfGlobalSections stageTwoSlopeProjectiveLineGrading
            (stageTwoSlopeProjectiveCoordinateMap x core) rfl (by omega)
            (MvPolynomial.isHomogeneous_X AlgNum none)) ≫
        ((X x).basicOpen (u x core)).topIso.hom ≫
        ((X x).basicOpen (u x core)).topIso.inv ≫
        (sourceChartSectionsIso x core).symm.hom ≫
        (Scheme.ΓSpecIso (.of (Localization.Away (u x core)))).hom =
      (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none)
          (by omega)).inv ≫
        CommRingCat.ofHom (affineLocalizationMap x core) := by
  rw [Iso.hom_inv_id_assoc]
  have hto :
      Proj.toBasicOpenOfGlobalSections stageTwoSlopeProjectiveLineGrading
          (stageTwoSlopeProjectiveCoordinateMap x core) rfl (by omega)
          (MvPolynomial.isHomogeneous_X AlgNum none) =
        (sourceChartIso x core).hom ≫
          Spec.map (CommRingCat.ofHom (affineLocalizationMap x core)) ≫
          (Proj.basicOpenIsoSpec stageTwoSlopeProjectiveLineGrading
            (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none)
            (by omega)).inv := by
    rfl
  rw [hto]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rw [sourceChartSectionsIso_cancel_assoc x core
    (Scheme.ΓSpecIso (.of (Localization.Away (u x core)))).hom]
  have hspec := Scheme.ΓSpecIso_naturality
    (CommRingCat.ofHom (affineLocalizationMap x core))
  rw [← Iso.eq_comp_inv] at hspec
  rw [hspec]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [targetChartCancel_assoc]

private theorem genericMap_app_aligned (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeGenericMap x core).app stageTwoSlopeProjectiveAffineChart ≫
        (X x).presheaf.map
          (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
            stageTwoSlopeProjectiveLineGrading
            (stageTwoSlopeProjectiveCoordinateMap x core)
            (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
            (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)).symm).op.hom ≫
        ((X x).basicOpen (u x core)).topIso.inv ≫
        (sourceChartSectionsIso x core).symm.hom ≫
        (Scheme.ΓSpecIso (.of (Localization.Away (u x core)))).hom =
      (Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X none) (MvPolynomial.isHomogeneous_X AlgNum none)
          (by omega)).inv ≫
        CommRingCat.ofHom (affineLocalizationMap x core) := by
  have hpre := Proj.fromOfGlobalSections_preimage_basicOpen
    stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
    (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)
  have hcast := Scheme.Hom.appLE_map
    (stageTwoSlopeGenericMap x core)
    (U := stageTwoSlopeProjectiveAffineChart)
    (V := stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart)
    (V' := (X x).basicOpen (u x core))
    (by rfl) ((eqToIso hpre.symm).op.hom)
  rw [Scheme.Hom.appLE_eq_app] at hcast
  have hres := Proj.fromOfGlobalSections_resLE
    stageTwoSlopeProjectiveLineGrading
    (stageTwoSlopeProjectiveCoordinateMap x core)
    (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
    (r := MvPolynomial.X none) (by omega)
    (MvPolynomial.isHomogeneous_X AlgNum none)
  have happ := congrArg Scheme.Hom.appTop hres
  simp only [Scheme.Hom.resLE_app_top] at happ
  have happ' := congrArg (fun q =>
    stageTwoSlopeProjectiveAffineChart.topIso.inv ≫ q ≫
      ((X x).basicOpen (u x core)).topIso.hom) happ
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at happ'
  rw [← Category.assoc]
  rw [← Category.assoc]
  rw [hcast]
  simp only [stageTwoSlopeGenericMap]
  rw [happ']
  exact toBasicOpen_appTop_aligned x core

@[simp]
private theorem affineLocalizationMap_base (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) (r : AlgNum) :
    affineLocalizationMap x core
        (optionHeadBaseToAway (σ := PUnit.{1}) r) =
      algebraMap Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
        (Localization.Away (u x core))
        ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
          (algebraMap AlgNum (stageTwoValueField (x 0) (x 1)) r)) := by
  have hval :
      HomogeneousLocalization.val
          (optionHeadBaseToAway (σ := PUnit.{1}) r) =
        algebraMap (MvPolynomial (Option PUnit.{1}) AlgNum)
          (Localization.Away
            (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum))
          (MvPolynomial.C r) := by
    change Localization.mk (MvPolynomial.C r) ⟨1, by exact Submonoid.one_mem _⟩ = _
    rw [Localization.mk_eq_mk']
    exact IsLocalization.mk'_one _ _
  rw [affineLocalizationMap_apply, hval]
  simp only [IsLocalization.Away.map, IsLocalization.map_eq]
  simp [stageTwoSlopeProjectiveCoordinateMap]

@[simp]
private theorem affineLocalizationMap_coordinate (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    affineLocalizationMap x core
        (optionHeadAffineCoordinate (R := AlgNum) PUnit.unit) =
      algebraMap Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
        (Localization.Away (u x core))
        ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
          core.rho) := by
  have hval :
      HomogeneousLocalization.val
          (optionHeadAffineCoordinate (R := AlgNum) PUnit.unit) =
        Localization.mk (MvPolynomial.X (some PUnit.unit))
          ⟨MvPolynomial.X none ^ 1, by exact ⟨1, rfl⟩⟩ := by
    simp [optionHeadAffineCoordinate, HomogeneousLocalization.Away.val_mk]
  rw [affineLocalizationMap_apply, hval, Localization.mk_eq_mk']
  simp only [IsLocalization.Away.map, IsLocalization.map_mk']
  simp only [map_pow, stageTwoSlopeProjectiveCoordinateMap_X_zero,
    stageTwoSlopeProjectiveCoordinateMap_X_one, one_pow]
  change IsLocalization.mk' (Localization.Away (u x core))
      ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
        core.rho) 1 = _
  exact IsLocalization.mk'_one (Localization.Away (u x core))
    ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
      core.rho)

@[simp]
private theorem affineChartRingEquiv_base (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) (r : AlgNum) :
    (stageTwoSlopeCoordinateRing x core).val
        (stageTwoSlopeProjectiveAffineChartRingEquiv x core
          (optionHeadBaseToAway (σ := PUnit.{1}) r)) =
      algebraMap AlgNum (stageTwoValueField (x 0) (x 1)) r := by
  change (Polynomial.aeval core.rho)
      (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (optionHeadAwayToPolynomial (R := AlgNum) (σ := PUnit.{1})
          (optionHeadBaseToAway (σ := PUnit.{1}) r))) = _
  rw [optionHeadAwayToPolynomial_base]
  simp

@[simp]
private theorem affineChartRingEquiv_coordinate (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeCoordinateRing x core).val
        (stageTwoSlopeProjectiveAffineChartRingEquiv x core
          (optionHeadAffineCoordinate (R := AlgNum) PUnit.unit)) = core.rho := by
  change (Polynomial.aeval core.rho)
      (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
        (optionHeadAwayToPolynomial (R := AlgNum) (σ := PUnit.{1})
          (optionHeadAffineCoordinate (R := AlgNum) PUnit.unit))) = _
  rw [optionHeadAwayToPolynomial_affineCoordinate]
  simp

private theorem affineLocalizationMap_to_value (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (sourceAwayValueRingEquiv x core).toRingHom.comp
        (affineLocalizationMap x core) =
      (stageTwoSlopeCoordinateRing x core).val.toRingHom.comp
        (stageTwoSlopeProjectiveAffineChartRingEquiv x core).toRingEquiv.toRingHom := by
  let dehomInv := optionHeadPolynomialToAway (R := AlgNum) (σ := PUnit.{1})
  have hcomp :
      ((sourceAwayValueRingEquiv x core).toRingHom.comp
          (affineLocalizationMap x core)).comp dehomInv =
        ((stageTwoSlopeCoordinateRing x core).val.toRingHom.comp
          (stageTwoSlopeProjectiveAffineChartRingEquiv x core).toRingEquiv.toRingHom).comp
            dehomInv := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, dehomInv, optionHeadPolynomialToAway,
        MvPolynomial.eval₂Hom_C]
      rw [affineLocalizationMap_base]
      change sourceAwayValueRingEquiv x core
          (algebraMap
            Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
            (Localization.Away (u x core))
            ((Scheme.ΓSpecIso
              (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
              (algebraMap AlgNum (stageTwoValueField (x 0) (x 1)) r))) =
        (stageTwoSlopeCoordinateRing x core).val
          (stageTwoSlopeProjectiveAffineChartRingEquiv x core
            (optionHeadBaseToAway (σ := PUnit.{1}) r))
      rw [sourceAwayValueRingEquiv_algebraMap, affineChartRingEquiv_base]
      simp
    · intro i
      rcases i with ⟨⟩
      simp only [RingHom.comp_apply, dehomInv, optionHeadPolynomialToAway,
        MvPolynomial.eval₂Hom_X']
      rw [affineLocalizationMap_coordinate]
      change sourceAwayValueRingEquiv x core
          (algebraMap
            Γ(Spec (.of (stageTwoValueField (x 0) (x 1))), ⊤)
            (Localization.Away (u x core))
            ((Scheme.ΓSpecIso
              (.of (stageTwoValueField (x 0) (x 1)))).inv.hom core.rho)) =
        (stageTwoSlopeCoordinateRing x core).val
          (stageTwoSlopeProjectiveAffineChartRingEquiv x core
            (optionHeadAffineCoordinate (R := AlgNum) PUnit.unit))
      rw [sourceAwayValueRingEquiv_algebraMap, affineChartRingEquiv_coordinate]
      simp
  have hsurj : Function.Surjective dehomInv := by
    intro z
    refine ⟨optionHeadAwayToPolynomial (R := AlgNum) (σ := PUnit.{1}) z, ?_⟩
    apply optionHeadAwayToPolynomial_injective
    unfold dehomInv
    exact RingHom.congr_fun optionHeadAwayToPolynomial_comp_polynomialToAway _
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := hsurj z
  exact RingHom.congr_fun hcomp p

/-- Under the aligned chart identifications, the generic projective section map is exactly the
inclusion of the polynomial slope coordinate ring into the value field. -/
theorem stageTwoSlopeGenericAffineChart_app_compatibility (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core).toRingHom.comp
        ((stageTwoSlopeGenericMap x core).app
          stageTwoSlopeProjectiveAffineChart).hom =
      (stageTwoSlopeCoordinateRing x core).val.toRingHom.comp
        (stageTwoSlopeProjectiveAffineChartSectionsRingEquiv x core).toRingHom := by
  apply RingHom.ext
  intro z
  change stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core
      (((stageTwoSlopeGenericMap x core).app
        stageTwoSlopeProjectiveAffineChart).hom z) =
    (stageTwoSlopeCoordinateRing x core).val
      (stageTwoSlopeProjectiveAffineChartSectionsRingEquiv x core z)
  rw [stageTwoSlopeGenericAffineChartSectionsRingEquivAligned_apply,
    projectiveAffineChartSectionsRingEquiv_apply]
  change sourceAwayValueRingEquiv x core
      ((Scheme.ΓSpecIso (.of (Localization.Away (u x core)))).hom.hom
        ((sourceChartSectionsIso x core).symm.hom.hom
          (((X x).basicOpen (u x core)).topIso.inv.hom
            (((X x).presheaf.map
              (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
                stageTwoSlopeProjectiveLineGrading
                (stageTwoSlopeProjectiveCoordinateMap x core)
                (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
                (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)).symm).op.hom).hom
              (((stageTwoSlopeGenericMap x core).app
                stageTwoSlopeProjectiveAffineChart).hom z))))) =
    (stageTwoSlopeCoordinateRing x core).val
      (stageTwoSlopeProjectiveAffineChartRingEquiv x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)).inv.hom z))
  have hcat := genericMap_app_aligned x core
  have hring := congrArg CommRingCat.Hom.hom hcat
  have hz := congrArg (fun q => sourceAwayValueRingEquiv x core q)
    (RingHom.congr_fun hring z)
  simp only [CategoryTheory.comp_apply] at hz
  have hloc := RingHom.congr_fun (affineLocalizationMap_to_value x core)
    ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
      (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
      (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)).inv.hom z)
  simp only [RingHom.comp_apply] at hloc
  change sourceAwayValueRingEquiv x core
      (affineLocalizationMap x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)).inv.hom z)) =
    (stageTwoSlopeCoordinateRing x core).val
      (stageTwoSlopeProjectiveAffineChartRingEquiv x core
        ((Proj.basicOpenIsoAway stageTwoSlopeProjectiveLineGrading
          (MvPolynomial.X none : MvPolynomial (Option PUnit.{1}) AlgNum)
          (MvPolynomial.isHomogeneous_X AlgNum none) (by omega)).inv.hom z)) at hloc
  exact hz.trans hloc

private theorem sourceChartIso_inv_ι_toSpecΓ (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (sourceChartIso x core).inv ≫ ((X x).basicOpen (u x core)).ι ≫
        (X x).toSpecΓ =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X x, ⊤) (Localization.Away (u x core)))) := by
  rw [← cancel_epi (sourceChartIso x core).hom]
  simp only [Iso.hom_inv_id_assoc]
  unfold sourceChartIso sourceChartMap
  simp only [asIso_hom, Category.assoc]
  rw [basicOpenIsoSpecAway_hom_SpecMap]
  simp

private theorem sourceChartSections_algebraMap (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    (X x).presheaf.map
          (homOfLE (show (X x).basicOpen (u x core) ≤ ⊤ from le_top)).op ≫
        ((X x).basicOpen (u x core)).topIso.inv ≫
        (sourceChartSectionsIso x core).symm.hom ≫
        (Scheme.ΓSpecIso (.of (Localization.Away (u x core)))).hom =
      CommRingCat.ofHom
        (algebraMap Γ(X x, ⊤) (Localization.Away (u x core))) := by
  have hmap := congrArg Scheme.Hom.appTop
    (sourceChartIso_inv_ι_toSpecΓ x core)
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at hmap
  rw [← cancel_epi (Scheme.ΓSpecIso (.of Γ(X x, ⊤))).hom]
  rw [← Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (algebraMap Γ(X x, ⊤) (Localization.Away (u x core))))]
  rw [← hmap]
  simp only [Category.assoc]
  congr 1

/-- The localization-aligned identification of source chart sections is the canonical
identification obtained from the equality of the pulled-back chart with the whole spectrum. -/
theorem stageTwoSlopeGenericAffineChartSectionsRingEquivAligned_eq
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core =
      stageTwoSlopeGenericAffineChartSectionsRingEquiv x core := by
  apply RingEquiv.ext
  intro z
  rw [stageTwoSlopeGenericAffineChartSectionsRingEquivAligned_apply]
  let w : Γ(X x, ⊤) :=
    ((X x).presheaf.map
      (eqToHom (stageTwoSlopeGenericMap_preimage_affineChart x core).symm).op).hom z
  unfold stageTwoSlopeGenericAffineChartSectionsRingEquiv
  change sourceAwayValueRingEquiv x core _ =
    (Scheme.ΓSpecIso (.of (K x))).hom.hom w
  rw [← sourceAwayValueRingEquiv_algebraMap x core w]
  congr 1
  have htransport :
      (((X x).presheaf.mapIso
        (eqToIso (Proj.fromOfGlobalSections_preimage_basicOpen
          stageTwoSlopeProjectiveLineGrading
          (stageTwoSlopeProjectiveCoordinateMap x core)
          (stageTwoSlopeProjectiveCoordinateMap_irrelevant x core)
          (by omega) (MvPolynomial.isHomogeneous_X AlgNum none)).symm).op).hom.hom z) =
        ((X x).presheaf.map
          (homOfLE (show (X x).basicOpen (u x core) ≤ ⊤ from le_top)).op).hom w := by
    dsimp only [w]
    change ((X x).presheaf.map _).hom z =
      ((X x).presheaf.map _).hom (((X x).presheaf.map _).hom z)
    rw [← Functor.map_comp_apply]
    rfl
  simp only [Iso.trans_hom, CategoryTheory.comp_apply]
  rw [htransport]
  have hsections := congrArg CommRingCat.Hom.hom
    (sourceChartSections_algebraMap x core)
  exact RingHom.congr_fun hsections w

end
end GaloisForLFunctions.RHTower
