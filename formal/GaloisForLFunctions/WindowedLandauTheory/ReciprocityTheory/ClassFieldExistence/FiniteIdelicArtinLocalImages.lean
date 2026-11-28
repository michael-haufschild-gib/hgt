import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FinitePrimeHilbertFields
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinRestriction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinFrobenius
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicArtinNormKernel
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicNormSinglePlace

/-! Finite local ideles map into decomposition groups, and local
integral units map into inertia. Both assertions follow by restriction
to the corresponding fixed field. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField WithZero
open GaloisForLFunctions
open scoped GlobalTheory.Reciprocity.AdicLiesOver IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local instance : CommGroup Gal(L/K) :=
  { (inferInstance : Group Gal(L/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (E : IntermediateField K L) [IsAbelianGalois K E] : CommGroup Gal(E/K) :=
  { (inferInstance : Group Gal(E/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (E : IntermediateField K L) : Fintype Gal(E/K) := Fintype.ofFinite _

private theorem restrictNormalHom_fixedField_ker (H : Subgroup Gal(L/K))
    [Normal K (fixedField H)] : (AlgEquiv.restrictNormalHom (fixedField H)).ker = H :=
  (fixedField H).restrictNormalHom_ker.trans (fixingSubgroup_fixedField H)

theorem finiteIdelicArtin_finiteEmbedding_mem_inertia
    (f : IdeleGroup K →* Gal(L/K)) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ x : Kˣ, f (diagonal K x) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : (v.adicCompletion K)ˣ) (hx : x ∈ unitsLevel v 0) :
    f (finiteEmbedding v x) ∈ w.asIdeal.inertia Gal(L/K) := by
  let H := w.asIdeal.inertia Gal(L/K)
  let E := fixedField H
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  let u := w.under (𝓞 E)
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  have hu : u.asIdeal.ramificationIdx (𝓞 K) = 1 := unramified_at_inertia_fixedField v w
  let g := (AlgEquiv.restrictNormalHom E).comp f
  have hg := isFiniteIdelicArtin_restrict E f hf hd
  have h := finiteIdelicArtin_finiteEmbedding_of_unramified g hg v
    (isUnramifiedPrime_of_ramificationIdx_eq_one v u hu) x
  rw [(mem_unitsLevel.mp hx).1, log_one, neg_zero, zpow_zero] at h
  change f (finiteEmbedding v x) ∈ H
  rw [← restrictNormalHom_fixedField_ker H]
  exact h

/-- Norms from a finite completion are killed by the finite global Artin map. -/
theorem finiteIdelicArtin_eq_one_on_single_local_norm
    (f : IdeleGroup K →* Gal(L/K)) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ x : Kˣ, f (diagonal K x) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : finitePlacesAbove L v) (y : (w.val.adicCompletion L)ˣ) :
    f (finiteEmbedding v (Units.map (Algebra.norm (v.adicCompletion K)) y)) = 1 := by
  change finiteEmbedding v (Units.map (Algebra.norm (v.adicCompletion K)) y) ∈ f.ker
  rw [← ideleNorm_finiteEmbedding v w, finiteIdelicArtin_ker_eq_diagonal_sup_ideleNorm f hf hd]
  exact (show (ideleNorm (K := K) (L := L)).range ≤
    (diagonal K).range ⊔ (ideleNorm (K := K) (L := L)).range from le_sup_right)
    ⟨finiteEmbedding w.val y, rfl⟩

theorem finiteIdelicArtin_finiteEmbedding_mem_decomposition
    (f : IdeleGroup K →* Gal(L/K)) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ x : Kˣ, f (diagonal K x) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : (v.adicCompletion K)ˣ) :
    f (finiteEmbedding v x) ∈ MulAction.stabilizer Gal(L/K) w.asIdeal := by
  let H := MulAction.stabilizer Gal(L/K) w.asIdeal
  let E := fixedField H
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  let u := w.under (𝓞 E)
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  have h := split_at_decomposition_fixedField v w
  have he : Module.finrank (v.adicCompletion K) (u.adicCompletion E) = 1 := by
    rw [finiteCompletion_finrank_eq_ramification_mul_inertia E v u, h.1, h.2, one_mul]
  let u' : finitePlacesAbove E v := ⟨u, (mem_finitePlacesAbove E v u).mpr inferInstance⟩
  let g := (AlgEquiv.restrictNormalHom E).comp f
  have hg := isFiniteIdelicArtin_restrict E f hf hd
  have hgd (a : Kˣ) : g (diagonal K a) = 1 := by
    change AlgEquiv.restrictNormalHom E (f (diagonal K a)) = 1
    rw [hd, map_one]
  let y := Units.map (algebraMap (v.adicCompletion K) (u.adicCompletion E)).toMonoidHom x
  have hx : Units.map (Algebra.norm (v.adicCompletion K)) y = x := by
    apply Units.ext
    change Algebra.norm (v.adicCompletion K) (algebraMap (v.adicCompletion K) (u.adicCompletion E)
      (x : v.adicCompletion K)) = x.val
    rw [Algebra.norm_algebraMap, he, pow_one]
  have hG := finiteIdelicArtin_eq_one_on_single_local_norm g hg hgd v u' y
  change g (finiteEmbedding v (Units.map (Algebra.norm (v.adicCompletion K)) y)) = 1 at hG
  rw [hx] at hG
  change f (finiteEmbedding v x) ∈ H
  rw [← restrictNormalHom_fixedField_ker H]
  exact hG

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_finiteEmbedding_mem_inertia
#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_finiteEmbedding_mem_decomposition
