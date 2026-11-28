import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinLocalImages
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerFactorOfAnInflatedRepresentation

/-! At any finite place, the idelic Artin symbol modulo inertia is the
arithmetic residue Frobenius raised to the local additive valuation. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField WithZero GaloisForLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local instance (E : IntermediateField K L) [IsAbelianGalois K E] : CommGroup Gal(E/K) :=
  { (inferInstance : Group Gal(E/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (E : IntermediateField K L) : Fintype Gal(E/K) := Fintype.ofFinite _

private theorem restrictArithFrob_eq_frobeniusElement (E : IntermediateField K L)
    [NumberField E] [IsAbelianGalois K E]
    (v : HeightOneSpectrum (𝓞 K)) (hv : IsUnramifiedPrime K E Gal(E/K) v)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) :
    AlgEquiv.restrictNormalHom E σ = frobeniusElement K E Gal(E/K) v := by
  let u := w.under (𝓞 E)
  letI := u.isMaximal
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  let r : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have ha (τ : Gal(L/K)) (a : 𝓞 E) :
      algebraMap (𝓞 E) (𝓞 L) (r τ • a) = τ • algebraMap (𝓞 E) (𝓞 L) a :=
    RingOfIntegers.ext (τ.restrictNormal_commutes E (a : E))
  have hu : IsArithFrobAt (𝓞 K) (r σ) u.asIdeal := isArithFrobAt_map_under r ha hσ
  have h := hu.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 K) Gal(E/K) u.asIdeal)
  rw [hv u.asIdeal inferInstance inferInstance, Subgroup.mem_bot,
    arithFrobAt_eq_frobeniusElement hv u.asIdeal] at h
  exact mul_inv_eq_one.mp h

theorem finiteIdelicArtin_finiteEmbedding_div_frob_mem_inertia
    (f : IdeleGroup K →* Gal(L/K)) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ x : Kˣ, f (diagonal K x) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (σ : Gal(L/K)) (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal) (x : (v.adicCompletion K)ˣ) :
    f (finiteEmbedding v x) / σ ^ (-log (Valued.v (x : v.adicCompletion K))) ∈
      w.asIdeal.inertia Gal(L/K) := by
  let H := w.asIdeal.inertia Gal(L/K)
  let E := fixedField H
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  let u := w.under (𝓞 E)
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  have hv := isUnramifiedPrime_of_ramificationIdx_eq_one v u (unramified_at_inertia_fixedField v w)
  let r : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hg := isFiniteIdelicArtin_restrict E f hf hd
  have he := finiteIdelicArtin_finiteEmbedding_of_unramified (r.comp f) hg v hv x
  have he' := restrictArithFrob_eq_frobeniusElement E v hv w σ hσ
  have hker : r.ker = H := E.restrictNormalHom_ker.trans (fixingSubgroup_fixedField H)
  change _ ∈ H
  rw [← hker, MonoidHom.mem_ker, map_div, map_zpow]
  change (r.comp f) (finiteEmbedding v x) / (r σ) ^ _ = 1
  rw [he, he', div_self']

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_finiteEmbedding_div_frob_mem_inertia
