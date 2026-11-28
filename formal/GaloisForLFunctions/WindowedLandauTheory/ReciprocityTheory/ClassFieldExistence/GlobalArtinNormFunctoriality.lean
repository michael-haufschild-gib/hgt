import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.GlobalArtinInertiaImage
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicArtinBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicArtinTowerRestriction

/-! The global Artin map after an idelic norm agrees with restriction of
scalars of the corresponding automorphism. Each finite abelian stage
can be enlarged to include the field from which the norm is taken. -/

noncomputable section

open NumberField IntermediateField

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L]
  [NumberField L] [IsAlgClosure L Ω]

theorem globalArtin_ideleNorm_eq_toMaxAb
    (a : CompactIdeleClassQuotient K →* Gal(maximalAbelianExtension K Ω/K))
    (b : CompactIdeleClassQuotient L →* Gal(maximalAbelianExtension L Ω/L))
    (ha : MatchesFiniteIdelicArtin K Ω a) (hb : MatchesFiniteIdelicArtin L Ω b)
    (x : IdeleGroup L) (s : Gal(Ω/L)) (hx : b (toCompactIdeleClassQuotient L x) = toMaxAb L Ω s) :
    a (toCompactIdeleClassQuotient K (ideleNorm (K := K) x)) = toMaxAb K Ω (s.restrictScalars K) := by
  apply injective_restrictAbPi
  funext V
  let M := (V : IntermediateField K Ω)
  letI : FiniteDimensional K M := V.2.1
  letI : IsAbelianGalois K M := V.2.2
  letI : NumberField M := NumberField.of_module_finite K M
  let B := L ⊔ M
  let LB : L ≤ B := le_sup_left
  let MB : M ≤ B := le_sup_right
  letI : FiniteDimensional K B := inferInstance
  letI : Normal K B := inferInstance
  letI : IsAbelianGalois K B := isAbelianGalois_of_le_maximalAbelianExtension B
    (sup_le (le_maximalAbelianExtension L) (le_maximalAbelianExtension M))
  letI : NumberField B := NumberField.of_module_finite K B
  let T := IntermediateField.extendScalars LB
  letI : Algebra L B := (IntermediateField.inclusion LB).toRingHom.toAlgebra
  letI : IsScalarTower K L B :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion LB).comp_algebraMap.symm
  letI : IsScalarTower L B Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra K T := (inferInstance : Algebra K B)
  letI : IsScalarTower K T Ω := (inferInstance : IsScalarTower K B Ω)
  letI : IsScalarTower K L T := (inferInstance : IsScalarTower K L B)
  letI : IsAbelianGalois K T := (inferInstance : IsAbelianGalois K B)
  letI : FiniteDimensional K T := (inferInstance : FiniteDimensional K B)
  letI : NumberField T := (inferInstance : NumberField B)
  letI : IsAbelianGalois L T := IsAbelianGalois.tower_top K L T
  let W : finiteAbelianExtensions K Ω := ⟨B, inferInstance, inferInstance⟩
  let U : finiteAbelianExtensions L Ω := ⟨T, FiniteDimensional.right K L T, inferInstance⟩
  let f : IdeleGroup K →* Gal(T/K) := finiteStageArtin K Ω a W
  let g := finiteStageArtin L Ω b U
  let fm : IdeleGroup K →* Gal(M/K) := finiteStageArtin K Ω a V
  let j : Gal(T/L) →* Gal(T/K) := AlgEquiv.restrictScalarsHom K
  have hjact (σ : Gal(T/L)) (z : T) : j σ • z = σ • z := rfl
  have hNg := finiteIdelicArtin_comp_ideleNorm K L T j hjact f g
    (finiteStageArtin_isFiniteIdelicArtin K Ω a ha W)
    (finiteStageArtin_isFiniteIdelicArtin L Ω b hb U)
    (finiteStageArtin_diagonal K Ω a W) (finiteStageArtin_diagonal L Ω b U)
  have hg : g x = AlgEquiv.restrictNormalHom T s := by
    change restrictAbPi L Ω (b (toCompactIdeleClassQuotient L x)) U = _
    rw [hx, restrictAbPi_toMaxAb]
  have hj : j (g x) = AlgEquiv.restrictNormalHom T (s.restrictScalars K) := by
    rw [hg]
    apply AlgEquiv.ext
    intro z
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes s T z).trans
      (AlgEquiv.restrictNormal_commutes (s.restrictScalars K) T z).symm
  have hf : f (ideleNorm (K := K) x) = AlgEquiv.restrictNormalHom T (s.restrictScalars K) :=
    (DFunLike.congr_fun hNg x).trans hj
  letI : Algebra M T := (IntermediateField.inclusion MB).toRingHom.toAlgebra
  letI : IsScalarTower K M T :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion MB).comp_algebraMap.symm
  letI : IsScalarTower M T Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hr := finiteIdelicArtin_restrict_eq K M T f fm
    (finiteStageArtin_isFiniteIdelicArtin K Ω a ha W)
    (finiteStageArtin_isFiniteIdelicArtin K Ω a ha V)
    (finiteStageArtin_diagonal K Ω a W) (finiteStageArtin_diagonal K Ω a V)
  change fm (ideleNorm (K := K) x) = restrictAbPi K Ω (toMaxAb K Ω (s.restrictScalars K)) V
  rw [restrictAbPi_toMaxAb]
  let y := ideleNorm (K := K) x
  let r : Gal(T/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom M
  calc
    fm y = r (f y) := (DFunLike.congr_fun hr y).symm
    _ = r (AlgEquiv.restrictNormalHom T (s.restrictScalars K)) := congrArg r hf
    _ = AlgEquiv.restrictNormalHom M (s.restrictScalars K) :=
      (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply M T (s.restrictScalars K)).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.globalArtin_ideleNorm_eq_toMaxAb
