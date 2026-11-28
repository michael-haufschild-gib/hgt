import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinInertiaImage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinEquivariance
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicArtinTowerRestriction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RelativeAbelianStage

/-! Global Artin on a local coordinate commutes with conjugation by a
decomposition automorphism of the smaller field. Enlarge the finite
relative stages to stages normal over that field. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open scoped Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

private theorem exists_finiteAbelianStage_normalOver
    (R : IntermediateField L Ω) [FiniteDimensional L R] [IsAbelianGalois L R] :
    ∃ T : IntermediateField L Ω, R ≤ T ∧ FiniteDimensional L T ∧
      IsAbelianGalois L T ∧ IsGalois K (T.restrictScalars K) := by
  letI : FiniteDimensional K (R.restrictScalars K) := FiniteDimensional.trans K L R
  let B := normalClosure K (R.restrictScalars K) Ω
  let hB : L ≤ B := fun x hx =>
    IntermediateField.le_normalClosure (R.restrictScalars K) (R.algebraMap_mem (⟨x, hx⟩ : L))
  let T := IntermediateField.extendScalars hB
  letI : Algebra K T := (inferInstance : Algebra K B)
  letI : IsScalarTower K L T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : FiniteDimensional K T := normalClosure.is_finiteDimensional K (R.restrictScalars K) Ω
  letI : IsGalois K T := IsGalois.normalClosure K (R.restrictScalars K) Ω
  letI : FiniteDimensional L T := FiniteDimensional.right K L T
  letI : Normal L T := (IsGalois.tower_top_of_isGalois K L T).to_normal
  letI : IsAbelianGalois L T := isAbelianGalois_of_le_maximalAbelianExtension T
    (normalClosure_restrictScalars_le_maximalAbelianExtension L R)
  exact ⟨T, IntermediateField.le_normalClosure (R.restrictScalars K),
    inferInstance, inferInstance, IsGalois.normalClosure K (R.restrictScalars K) Ω⟩

private theorem relativeAutConj_restrictNormalHom
    {P : Type} [Field P] [Algebra K P] [Algebra L P] [Algebra P Ω]
    [IsScalarTower K P Ω] [IsScalarTower L P Ω] [IsScalarTower K L P]
    [Normal K P] [Normal L P]
    (t : Gal(Ω/K)) (s : Gal(Ω/L)) :
    relativeAutConj K L P (AlgEquiv.restrictNormalHom P t) (AlgEquiv.restrictNormalHom P s) =
      AlgEquiv.restrictNormalHom P (relativeAutConj K L Ω t s) := by
  let t' : Gal(P/K) := AlgEquiv.restrictNormalHom P t
  let s' : Gal(P/L) := AlgEquiv.restrictNormalHom P s
  have ht (z : P) : algebraMap P Ω (t' z) = t (algebraMap P Ω z) :=
    AlgEquiv.restrictNormal_commutes t P z
  have hs (z : P) : algebraMap P Ω (s' z) = s (algebraMap P Ω z) :=
    AlgEquiv.restrictNormal_commutes s P z
  have hi (z : P) : algebraMap P Ω (t'.symm z) = t.symm (algebraMap P Ω z) := by
    apply t.injective
    rw [← ht, t'.apply_symm_apply, t.apply_symm_apply]
  apply AlgEquiv.ext
  intro z
  apply (algebraMap P Ω).injective
  change algebraMap P Ω (relativeAutConj K L P t' s' z) = algebraMap P Ω
    ((relativeAutConj K L Ω t s).restrictNormal P z)
  rw [relativeAutConj_apply, ht, hs, hi, AlgEquiv.restrictNormal_commutes, relativeAutConj_apply]

theorem globalArtin_finiteEmbedding_conjugate
    (b : CompactIdeleClassQuotient L →* Gal(maximalAbelianExtension L Ω/L))
    (hb : MatchesFiniteIdelicArtin L Ω b)
    (t : Gal(Ω/K)) (ht : AlgEquiv.restrictNormalHom L t ∈ MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : (w.adicCompletion L)ˣ) (s : Gal(Ω/L))
    (hx : b (toCompactIdeleClassQuotient L (finiteEmbedding w x)) = toMaxAb L Ω s) :
    b (toCompactIdeleClassQuotient L (finiteEmbedding w
      (Units.map (decompositionMulEquiv v w ⟨AlgEquiv.restrictNormalHom L t, ht⟩).toMonoidHom x))) =
      toMaxAb L Ω (relativeAutConj K L Ω t s) := by
  let g : MulAction.stabilizer Gal(L/K) w.asIdeal := ⟨AlgEquiv.restrictNormalHom L t, ht⟩
  let y := Units.map (decompositionMulEquiv v w g).toMonoidHom x
  apply injective_restrictAbPi
  funext V
  let R := (V : IntermediateField L Ω)
  letI : FiniteDimensional L R := V.2.1
  letI : IsAbelianGalois L R := V.2.2
  letI : NumberField R := NumberField.of_module_finite L R
  obtain ⟨T, hRT, hTf, hTa, hTg⟩ := exists_finiteAbelianStage_normalOver K Ω L R
  letI : Algebra K T := (inferInstance : Algebra K (T.restrictScalars K))
  letI : IsScalarTower K T Ω := (inferInstance : IsScalarTower K (T.restrictScalars K) Ω)
  letI : IsScalarTower K L T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsGalois K T := hTg
  letI : FiniteDimensional L T := hTf
  letI : IsAbelianGalois L T := hTa
  letI : NumberField T := NumberField.of_module_finite L T
  let U : finiteAbelianExtensions L Ω := ⟨T, inferInstance, inferInstance⟩
  let f := finiteStageArtin L Ω b U
  let f₀ := finiteStageArtin L Ω b V
  let t' : Gal(T/K) := AlgEquiv.restrictNormalHom T t
  have hrt : AlgEquiv.restrictNormalHom L t' = AlgEquiv.restrictNormalHom L t :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L T t).symm
  have ht' : AlgEquiv.restrictNormalHom L t' ∈ MulAction.stabilizer Gal(L/K) w.asIdeal := hrt.symm ▸ ht
  have hconj := finiteIdelicArtin_finiteEmbedding_conjugate K L T f
    (finiteStageArtin_isFiniteIdelicArtin L Ω b hb U) (finiteStageArtin_diagonal L Ω b U) v w t' ht' x
  have hgt : (⟨AlgEquiv.restrictNormalHom L t', ht'⟩ : MulAction.stabilizer Gal(L/K) w.asIdeal) = g :=
    Subtype.ext hrt
  rw [hgt] at hconj
  have hfx : f (finiteEmbedding w x) = AlgEquiv.restrictNormalHom T s := by
    change restrictAbPi L Ω (b (toCompactIdeleClassQuotient L (finiteEmbedding w x))) U = _
    rw [hx, restrictAbPi_toMaxAb]
  have hre := relativeAutConj_restrictNormalHom K Ω L (P := T) t s
  have hy : f (finiteEmbedding w y) = AlgEquiv.restrictNormalHom T (relativeAutConj K L Ω t s) := by
    change f (finiteEmbedding w y) = _ at hconj
    rw [hconj, hfx, hre]
  letI : Algebra R T := (IntermediateField.inclusion hRT).toRingHom.toAlgebra
  letI : IsScalarTower L R T :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hRT).comp_algebraMap.symm
  letI : IsScalarTower R T Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hRf := finiteIdelicArtin_restrict_eq L R T f f₀
    (finiteStageArtin_isFiniteIdelicArtin L Ω b hb U)
    (finiteStageArtin_isFiniteIdelicArtin L Ω b hb V)
    (finiteStageArtin_diagonal L Ω b U) (finiteStageArtin_diagonal L Ω b V)
  change f₀ (finiteEmbedding w y) = restrictAbPi L Ω (toMaxAb L Ω (relativeAutConj K L Ω t s)) V
  rw [restrictAbPi_toMaxAb, ← hRf, MonoidHom.comp_apply, hy]
  exact (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply R T (relativeAutConj K L Ω t s)).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.globalArtin_finiteEmbedding_conjugate
