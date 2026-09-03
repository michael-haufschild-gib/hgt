import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeProjectiveFinite
import GaloisForLFunctions.HTGeometry.FunctionFieldPullback

/-!
# Function field of the projective stage-two slope normalization

The standard affine chart of the relative normalization has section ring equal to the concrete
integral closure already constructed inside the stage-two value field.  Passing to fraction fields
on that chart and then across its dominant open immersion identifies the function field of the
global projective normalization with the literal stage-two value field.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry TopologicalSpace

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-- Pullback of the standard slope chart to the projective relative normalization. -/
abbrev stageTwoSlopeProjectiveNormalizationAffineChart
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeProjectiveNormalization x core).Opens :=
  stageTwoSlopeProjectiveNormalizationToLine x core ⁻¹ᵁ
    stageTwoSlopeProjectiveAffineChart

/-- Sections of the normalized standard chart are exactly the concrete affine normalization
ring.  Both equivalences come from the actual normalization chart and its computed generic map. -/
noncomputable def stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Γ(stageTwoSlopeProjectiveNormalization x core,
      stageTwoSlopeProjectiveNormalizationAffineChart x core) ≃+*
      stageTwoSlopeAffineNormalizationRing x core :=
  (commRingCatIsoRingEquiv
    ((stageTwoSlopeGenericMap x core).normalizationObjIso
      stageTwoSlopeProjectiveAffineChart_isAffine)).trans
    (integralClosureRingEquivOfSquare
      ((stageTwoSlopeGenericMap x core).app
        stageTwoSlopeProjectiveAffineChart).hom
      (stageTwoSlopeCoordinateRing x core).val.toRingHom
      (stageTwoSlopeProjectiveAffineChartSectionsRingEquiv x core)
      (stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core)
      (stageTwoSlopeGenericAffineChart_app_compatibility x core))

/-- The pullback of the standard affine slope chart remains affine on the relative
normalization. -/
theorem stageTwoSlopeProjectiveNormalizationAffineChart_isAffine
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsAffineOpen (stageTwoSlopeProjectiveNormalizationAffineChart x core) := by
  exact stageTwoSlopeProjectiveAffineChart_isAffine.preimage
    (stageTwoSlopeProjectiveNormalizationToLine x core)

private theorem genericInclusion_mem_normalizationAffineChart
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (z : Spec (.of (stageTwoValueField (x 0) (x 1)))) :
    stageTwoSlopeProjectiveGenericInclusion x core z ∈
      stageTwoSlopeProjectiveNormalizationAffineChart x core := by
  change stageTwoSlopeProjectiveNormalizationToLine x core
      (stageTwoSlopeProjectiveGenericInclusion x core z) ∈
    stageTwoSlopeProjectiveAffineChart
  have hz : z ∈ stageTwoSlopeGenericMap x core ⁻¹ᵁ
      stageTwoSlopeProjectiveAffineChart := by
    rw [stageTwoSlopeGenericMap_preimage_affineChart]
    trivial
  rw [← Scheme.Hom.comp_apply,
    stageTwoSlopeProjectiveNormalization_factorization]
  exact hz

/-- The normalized standard chart contains the image of the source generic point. -/
noncomputable instance stageTwoSlopeProjectiveNormalizationAffineChart_nonempty
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Nonempty (stageTwoSlopeProjectiveNormalizationAffineChart x core) :=
  ⟨⟨stageTwoSlopeProjectiveGenericInclusion x core
      (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1))))),
    genericInclusion_mem_normalizationAffineChart x core _⟩⟩

/-- The normalized standard chart is dense: it contains the dense image of the concrete generic
field supplied by the relative-normalization construction. -/
noncomputable instance stageTwoSlopeProjectiveNormalizationAffineChart_ι_isDominant
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsDominant (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι := by
  constructor
  change Dense (Set.range
    (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι)
  rw [Scheme.Opens.range_ι]
  apply (stageTwoSlopeProjectiveGenericInclusion x core).denseRange.mono
  intro y hy
  rcases hy with ⟨z, rfl⟩
  exact genericInclusion_mem_normalizationAffineChart x core z

/-- The function field of the global projective relative normalization is the concrete stage-two
value field.  The equivalence passes through the actual normalized affine chart, not a proxy
curve. -/
noncomputable def stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoValueField (x 0) (x 1) ≃+*
      (stageTwoSlopeProjectiveNormalization x core).functionField := by
  let N := stageTwoSlopeProjectiveNormalization x core
  let U := stageTwoSlopeProjectiveNormalizationAffineChart x core
  let S := Γ(N, U)
  let R := stageTwoSlopeAffineNormalizationRing x core
  let eSR : S ≃+* R :=
    stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core
  letI : Nontrivial S := eSR.toRingHom.domain_nontrivial
  letI : NoZeroDivisors S :=
    Function.Injective.noZeroDivisors eSR eSR.injective eSR.map_zero eSR.map_mul
  letI : IsDomain S := NoZeroDivisors.to_isDomain S
  letI : Algebra S (Spec (.of S)).functionField := RingHom.toAlgebra
    (StructureSheaf.toStalk S (genericPoint (Spec (.of S)))).hom
  letI : IsFractionRing S (Spec (.of S)).functionField :=
    functionField_isFractionRing_of_affine (.of S)
  let eKSpec : stageTwoValueField (x 0) (x 1) ≃+*
      (Spec (.of S)).functionField :=
    @IsFractionRing.ringEquivOfRingEquiv
      R (stageTwoValueField (x 0) (x 1)) S
      (Spec (.of S)).functionField
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance eSR.symm
  let hU : IsAffineOpen U :=
    stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core
  exact eKSpec.trans
    ((Scheme.Iso.functionFieldPullbackRingEquiv hU.isoSpec).trans
      ((U.ι).functionFieldPullbackRingEquivOfOpenImmersion.symm))

private theorem normalizationFunctionFieldEquiv_algebraMap
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (r : stageTwoSlopeAffineNormalizationRing x core) :
    stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
        (algebraMap (stageTwoSlopeAffineNormalizationRing x core)
          (stageTwoValueField (x 0) (x 1)) r) =
      ((Scheme.Hom.functionFieldPullbackRingEquivOfOpenImmersion
          (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι).symm)
        ((Scheme.Iso.functionFieldPullbackRingEquiv
            (stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core).isoSpec)
          ((StructureSheaf.toStalk
              Γ(stageTwoSlopeProjectiveNormalization x core,
                stageTwoSlopeProjectiveNormalizationAffineChart x core)
              (genericPoint (Spec (.of
                Γ(stageTwoSlopeProjectiveNormalization x core,
                  stageTwoSlopeProjectiveNormalizationAffineChart x core))))).hom
            ((stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv
              x core).symm r))) := by
  dsimp only [stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv,
    RingEquiv.trans_apply]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

private theorem normalizationIsoSpec_functionFieldPullback_toStalk
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (s : Γ(stageTwoSlopeProjectiveNormalization x core,
      stageTwoSlopeProjectiveNormalizationAffineChart x core)) :
    (stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core).isoSpec.hom.functionFieldPullback
        ((StructureSheaf.toStalk
          Γ(stageTwoSlopeProjectiveNormalization x core,
            stageTwoSlopeProjectiveNormalizationAffineChart x core)
          (genericPoint (Spec (.of
            Γ(stageTwoSlopeProjectiveNormalization x core,
              stageTwoSlopeProjectiveNormalizationAffineChart x core))))).hom s) =
      (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme.presheaf.germ
        ⊤ (genericPoint
          (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme) trivial
        ((stageTwoSlopeProjectiveNormalizationAffineChart x core).topIso.inv.hom s) := by
  rw [show (StructureSheaf.toStalk
        Γ(stageTwoSlopeProjectiveNormalization x core,
          stageTwoSlopeProjectiveNormalizationAffineChart x core)
        (genericPoint (Spec (.of
          Γ(stageTwoSlopeProjectiveNormalization x core,
            stageTwoSlopeProjectiveNormalizationAffineChart x core))))).hom s =
      (Spec (.of Γ(stageTwoSlopeProjectiveNormalization x core,
        stageTwoSlopeProjectiveNormalizationAffineChart x core))).presheaf.germ
        ⊤ (genericPoint (Spec (.of
          Γ(stageTwoSlopeProjectiveNormalization x core,
            stageTwoSlopeProjectiveNormalizationAffineChart x core)))) trivial
        ((Scheme.ΓSpecIso (.of Γ(stageTwoSlopeProjectiveNormalization x core,
          stageTwoSlopeProjectiveNormalizationAffineChart x core))).inv.hom s) by rfl]
  trans (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme.presheaf.germ
      ⊤ (genericPoint
        (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme) trivial
      (((stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core).isoSpec.hom.appTop).hom
        ((Scheme.ΓSpecIso (.of Γ(stageTwoSlopeProjectiveNormalization x core,
          stageTwoSlopeProjectiveNormalizationAffineChart x core))).inv.hom s))
  · exact Scheme.Hom.functionFieldPullback_germ_appTop
      (stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core).isoSpec.hom _
  · congr 1
    rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_appTop]
    change (stageTwoSlopeProjectiveNormalizationAffineChart x core).topIso.inv.hom
        ((Scheme.ΓSpecIso (.of Γ(stageTwoSlopeProjectiveNormalization x core,
          stageTwoSlopeProjectiveNormalizationAffineChart x core))).hom.hom
          ((Scheme.ΓSpecIso (.of Γ(stageTwoSlopeProjectiveNormalization x core,
            stageTwoSlopeProjectiveNormalizationAffineChart x core))).inv.hom s)) = _
    rw [Iso.inv_hom_id_apply]

/-- The normalized affine slope chart contains the generic point of the projective
normalization. -/
theorem stageTwoSlopeProjectiveNormalizationAffineChart_genericPoint_mem
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    genericPoint (stageTwoSlopeProjectiveNormalization x core) ∈
      stageTwoSlopeProjectiveNormalizationAffineChart x core := by
  rw [← (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι.map_genericPoint_of_isDominant]
  exact (genericPoint
    (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme).property

private theorem normalizationOpenPullback_germ
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (s : Γ(stageTwoSlopeProjectiveNormalization x core,
      stageTwoSlopeProjectiveNormalizationAffineChart x core)) :
    (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι.functionFieldPullback
        ((stageTwoSlopeProjectiveNormalization x core).presheaf.germ
          (stageTwoSlopeProjectiveNormalizationAffineChart x core)
          (genericPoint (stageTwoSlopeProjectiveNormalization x core))
          (stageTwoSlopeProjectiveNormalizationAffineChart_genericPoint_mem x core) s) =
      (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme.presheaf.germ
        ⊤ (genericPoint
          (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme) trivial
        ((stageTwoSlopeProjectiveNormalizationAffineChart x core).topIso.inv.hom s) := by
  rw [Scheme.Hom.functionFieldPullback_germ]
  let i : ((stageTwoSlopeProjectiveNormalizationAffineChart x core).ι ⁻¹ᵁ
      stageTwoSlopeProjectiveNormalizationAffineChart x core) ⟶ (⊤ :
        (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme.Opens) :=
    homOfLE le_top
  rw [← (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme.presheaf.germ_res_apply
    i (genericPoint
      (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme)
    (by simpa using
      stageTwoSlopeProjectiveNormalizationAffineChart_genericPoint_mem x core)
    ((stageTwoSlopeProjectiveNormalizationAffineChart x core).topIso.inv.hom s)]
  congr 1
  rw [Scheme.Opens.ι_app_self, Scheme.Opens.topIso_inv]
  dsimp only [i]
  change _ = ((stageTwoSlopeProjectiveNormalization x core).presheaf.map _).hom
    (((stageTwoSlopeProjectiveNormalization x core).presheaf.map _).hom s)
  rw [← Functor.map_comp_apply]
  rfl

private theorem normalizationFunctionFieldEquiv_algebraMap_germ
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (r : stageTwoSlopeAffineNormalizationRing x core) :
    stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
        (algebraMap (stageTwoSlopeAffineNormalizationRing x core)
          (stageTwoValueField (x 0) (x 1)) r) =
      (stageTwoSlopeProjectiveNormalization x core).presheaf.germ
        (stageTwoSlopeProjectiveNormalizationAffineChart x core)
        (genericPoint (stageTwoSlopeProjectiveNormalization x core))
        (stageTwoSlopeProjectiveNormalizationAffineChart_genericPoint_mem x core)
        ((stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core).symm r) := by
  apply (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι.functionFieldPullback_injective
  rw [normalizationFunctionFieldEquiv_algebraMap]
  let q : (stageTwoSlopeProjectiveNormalizationAffineChart x core).toScheme.functionField :=
    (stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core).isoSpec.hom.functionFieldPullback
      ((StructureSheaf.toStalk
        Γ(stageTwoSlopeProjectiveNormalization x core,
          stageTwoSlopeProjectiveNormalizationAffineChart x core)
        (genericPoint (Spec (.of
          Γ(stageTwoSlopeProjectiveNormalization x core,
            stageTwoSlopeProjectiveNormalizationAffineChart x core))))).hom
        ((stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core).symm r))
  change (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι.functionFieldPullback
      ((Scheme.Hom.functionFieldPullbackRingEquivOfOpenImmersion
        (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι).symm q) = _
  change (Scheme.Hom.functionFieldPullbackRingEquivOfOpenImmersion
      (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι)
        ((Scheme.Hom.functionFieldPullbackRingEquivOfOpenImmersion
          (stageTwoSlopeProjectiveNormalizationAffineChart x core).ι).symm q) = _
  rw [RingEquiv.apply_symm_apply]
  dsimp only [q]
  rw [normalizationIsoSpec_functionFieldPullback_toStalk]
  rw [normalizationOpenPullback_germ]

private theorem normalization_appLE_aligned
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (r : stageTwoSlopeAffineNormalizationRing x core) :
    stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core
        (((stageTwoSlopeProjectiveGenericInclusion x core).appLE
          (stageTwoSlopeProjectiveNormalizationAffineChart x core)
          (stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart)
          (by simp [← Scheme.Hom.comp_preimage])).hom
          ((stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core).symm r)) =
      algebraMap (stageTwoSlopeAffineNormalizationRing x core)
        (stageTwoValueField (x 0) (x 1)) r := by
  have hn := (stageTwoSlopeGenericMap x core).normalizationObjIso_hom_val
    stageTwoSlopeProjectiveAffineChart_isAffine
  rw [← hn]
  simp only [CategoryTheory.comp_apply]
  let eNorm := commRingCatIsoRingEquiv
    ((stageTwoSlopeGenericMap x core).normalizationObjIso
      stageTwoSlopeProjectiveAffineChart_isAffine)
  let eInt := integralClosureRingEquivOfSquare
    ((stageTwoSlopeGenericMap x core).app
      stageTwoSlopeProjectiveAffineChart).hom
    (stageTwoSlopeCoordinateRing x core).val.toRingHom
    (stageTwoSlopeProjectiveAffineChartSectionsRingEquiv x core)
    (stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core)
    (stageTwoSlopeGenericAffineChart_app_compatibility x core)
  have heq :
      stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core =
        eNorm.trans eInt := rfl
  have hsections :
      ((stageTwoSlopeGenericMap x core).normalizationObjIso
        stageTwoSlopeProjectiveAffineChart_isAffine).hom.hom
          ((stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core).symm r) =
        eInt.symm r := by
    rw [heq]
    change eNorm (eNorm.symm (eInt.symm r)) = eInt.symm r
    exact eNorm.apply_symm_apply (eInt.symm r)
  rw [hsections]
  change stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core
      (eInt.symm r).1 = r.1
  change stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core
      ((stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core).symm r.1) = r.1
  exact (stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core).apply_symm_apply r.1

private theorem genericAffineChart_germ_eq_toStalk
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (s : Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
      stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart)) :
    (Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.germ
        (stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart)
        (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1)))))
        (by rw [stageTwoSlopeGenericMap_preimage_affineChart]; trivial) s =
      (StructureSheaf.toStalk (stageTwoValueField (x 0) (x 1))
        (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1)))))).hom
        (stageTwoSlopeGenericAffineChartSectionsRingEquiv x core s) := by
  unfold stageTwoSlopeGenericAffineChartSectionsRingEquiv
  change _ = (Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.germ
    ⊤ (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1))))) trivial
    ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).inv.hom
      ((Scheme.ΓSpecIso (.of (stageTwoValueField (x 0) (x 1)))).hom.hom
        (((Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.mapIso
          (eqToIso (stageTwoSlopeGenericMap_preimage_affineChart x core).symm).op).hom.hom s)))
  rw [Iso.hom_inv_id_apply]
  exact ((Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.germ_res_apply
    (eqToHom (stageTwoSlopeGenericMap_preimage_affineChart x core).symm)
    (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1))))) trivial s).symm

/-- The concrete function-field equivalence is coherent with pullback along the literal generic
inclusion: every element of the stage-two value field returns as the same rational function on
`Spec K`. -/
theorem stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv_pullback
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    (stageTwoSlopeProjectiveGenericInclusion x core).functionFieldPullback.hom.comp
        (stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core).toRingHom =
      (Scheme.specFunctionFieldAlgEquiv
        (stageTwoValueField (x 0) (x 1))).toRingHom := by
  apply IsFractionRing.ringHom_ext
    (A := stageTwoSlopeAffineNormalizationRing x core)
  intro r
  simp only [RingHom.comp_apply]
  change (stageTwoSlopeProjectiveGenericInclusion x core).functionFieldPullback
      (stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
        (algebraMap (stageTwoSlopeAffineNormalizationRing x core)
          (stageTwoValueField (x 0) (x 1)) r)) =
    Scheme.specFunctionFieldAlgEquiv
      (stageTwoValueField (x 0) (x 1))
      (algebraMap (stageTwoSlopeAffineNormalizationRing x core)
        (stageTwoValueField (x 0) (x 1)) r)
  rw [normalizationFunctionFieldEquiv_algebraMap_germ]
  rw [Scheme.Hom.functionFieldPullback_germ]
  let s := (stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core).symm r
  let V := stageTwoSlopeGenericMap x core ⁻¹ᵁ stageTwoSlopeProjectiveAffineChart
  let W := stageTwoSlopeProjectiveGenericInclusion x core ⁻¹ᵁ
    stageTwoSlopeProjectiveNormalizationAffineChart x core
  have hVW : V ≤ W := by
    dsimp only [V, W]
    simp [← Scheme.Hom.comp_preimage]
  trans (Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.germ
      V (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1)))))
      (by
        dsimp only [V]
        rw [stageTwoSlopeGenericMap_preimage_affineChart]
        trivial)
      (((stageTwoSlopeProjectiveGenericInclusion x core).appLE
        (stageTwoSlopeProjectiveNormalizationAffineChart x core) V hVW).hom s)
  · exact ((Spec (.of (stageTwoValueField (x 0) (x 1)))).presheaf.germ_res_apply
      (homOfLE hVW)
      (genericPoint (Spec (.of (stageTwoValueField (x 0) (x 1)))))
      (by
        dsimp only [V]
        rw [stageTwoSlopeGenericMap_preimage_affineChart]
        trivial)
      (((stageTwoSlopeProjectiveGenericInclusion x core).app
        (stageTwoSlopeProjectiveNormalizationAffineChart x core)).hom s)).symm
  · dsimp only [V, s]
    rw [genericAffineChart_germ_eq_toStalk]
    have haligned := normalization_appLE_aligned x core r
    rw [stageTwoSlopeGenericAffineChartSectionsRingEquivAligned_eq] at haligned
    rw [haligned]
    letI := Scheme.specFunctionFieldAlgebra
      (stageTwoValueField (x 0) (x 1))
    exact ((Scheme.specFunctionFieldAlgEquiv
      (stageTwoValueField (x 0) (x 1))).commutes r.1).symm

end

end GaloisForLFunctions.RHTower
