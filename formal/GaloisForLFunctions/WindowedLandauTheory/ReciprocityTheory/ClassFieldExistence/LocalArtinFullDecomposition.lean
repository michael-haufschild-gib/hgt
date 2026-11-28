import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinPrimeDegreeCyclotomic
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeOrderAbelianQuotient

/-! At a prime whose decomposition group is the full abelian Galois
group, any proper local Artin image would give a prime-degree quotient
on which the local Artin map is trivial. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField GaloisForLFunctions
open scoped IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (E : IntermediateField K L) [IsAbelianGalois K E] : CommGroup Gal(E/K) :=
  { (inferInstance : Group Gal(E/K)) with mul_comm := IsMulCommutative.is_comm.comm }

local instance (E : IntermediateField K L) : Fintype Gal(E/K) := Fintype.ofFinite _

theorem finiteIdelicArtin_surjective_at_full_decomposition
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hw : MulAction.stabilizer G w.asIdeal = ⊤) :
    Function.Surjective (f.comp (finiteEmbedding v)) := by
  classical
  let p := f.comp (finiteEmbedding v)
  apply MonoidHom.range_eq_top.mp
  by_contra hn
  letI : Finite (Subgroup G) :=
    Finite.of_injective (fun J : Subgroup G => (J : Set G)) SetLike.coe_injective
  obtain ⟨H, hH, hP⟩ := (eq_top_or_exists_le_coatom p.range).resolve_left hn
  let E := fixedField H
  letI : NumberField E := NumberField.of_module_finite K E
  letI : IsAbelianGalois K E := IsAbelianGalois.of_algHom E.val
  let u := w.under (𝓞 E)
  letI : u.asIdeal.LiesOver v.asIdeal := liesOver_under_intermediateField v w E
  let r : G →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hR : Function.Surjective r :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := L)
  have hk : r.ker = H := E.restrictNormalHom_ker.trans (fixingSubgroup_fixedField H)
  have he : Module.finrank K E = Nat.card (G ⧸ H) := by
    rw [← IsGalois.card_aut_eq_finrank,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hR).toEquiv, hk]
  have hp := prime_card_quotient_of_isCoatom H hH
  have hu : MulAction.stabilizer Gal(E/K) u.asIdeal = ⊤ := by
    rw [← map_stabilizer_restrictNormalHom K E L w, hw, Subgroup.map_top_of_surjective _ hR]
  obtain ⟨m, g, -, -, hgd, hgu, hgm⟩ := exists_finite_idelic_artin K E Gal(E/K)
  have hg : IsFiniteIdelicArtin g := ⟨m, hgu, hgm⟩
  have hr : r.comp f = g := finiteIdelicArtin_restrict_eq K E L f g hf hg hd hgd
  have hs := finiteIdelicArtin_surjective_at_full_decomposition_of_prime_degree hp he g hg hgd v u hu
  haveI : Nontrivial Gal(E/K) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsGalois.card_aut_eq_finrank, he]
    exact hp.one_lt)
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Gal(E/K))
  obtain ⟨x, hx⟩ := hs σ
  apply hσ
  rw [← hx]
  change g (finiteEmbedding v x) = 1
  rw [← hr]
  change r (p x) = 1
  apply MonoidHom.mem_ker.mp
  rw [hk]
  exact hP ⟨x, rfl⟩

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_surjective_at_full_decomposition
