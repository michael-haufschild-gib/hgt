import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelesWithFiniteSupport
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FiniteIdelicArtin
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RealNormSigns
import GaloisForLFunctions.RHTower.Artin.TheKernelOfTheArtinMapIsTheNormGroup

/-! An everywhere unramified abelian extension in which a set of ideal
class generators splits, including all real places, is trivial. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped nonZeroDivisors

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (G : Type u) [CommGroup G] [Fintype G] [MulSemiringAction G L] [IsGaloisGroup G K L]

private theorem artinMap_principal_eq_one_of_split_real
    (hu : ∀ v, IsUnramifiedPrime K L G v)
    (hr : ∀ v : {w : InfinitePlace K // w.IsReal},
      ∃ w : {w : InfinitePlace L // w.IsReal}, w.val.comap (algebraMap K L) = v.val)
    (a : Kˣ) : artinMap K L G (toPrincipalIdeal (𝓞 K) K a) = 1 := by
  obtain ⟨m, hm, hs, hrec⟩ := exists_ideal_rayPrincipal_le_ker_artinMap K L G
  let M : Modulus K := ⟨m, hm, Set.univ⟩
  obtain ⟨b, hb⟩ := exists_norm_with_real_signs G hr a
  let c := Units.map (Algebra.norm K : L →* K) b
  have hc : artinMap K L G (toPrincipalIdeal (𝓞 K) K c) = 1 := by
    rw [show toPrincipalIdeal (𝓞 K) K c = idealNormHom K L (toPrincipalIdeal (𝓞 L) L b) from
      (idealNormHom_toPrincipalIdeal K L b).symm]
    exact artinMap_idealNormHom K L G _
  have ha : toPrincipalIdeal (𝓞 K) K (a / c) ∈ rayPrincipal M := by
    refine ⟨a / c, ?_, rfl⟩
    change a / c ∈ rayGroup M
    have h : a / c ∈ rayUnits M := (mem_rayUnits M).mpr
      ⟨fun v hv => ((hs v).mp hv (hu v)).elim, fun w _ => hb w⟩
    exact (rayUnits_eq M) ▸ h
  have he := MonoidHom.mem_ker.mp (hrec ha)
  rwa [map_div, map_div, hc, _root_.div_one] at he

theorem subsingleton_of_split_class_generators
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : (diagonal K).range ⊔ supportedIdeles (K := K) S = ⊤)
    (hu : ∀ v, IsUnramifiedPrime K L G v)
    (hf : ∀ v ∈ S, frobeniusElement K L G v = 1)
    (hr : ∀ v : {w : InfinitePlace K // w.IsReal},
      ∃ w : {w : InfinitePlace L // w.IsReal}, w.val.comap (algebraMap K L) = v.val) :
    Subsingleton G := by
  have hall (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : artinMap K L G I = 1 := by
    obtain ⟨x, rfl⟩ := toFractionalIdeal_surjective I
    obtain ⟨_, ⟨a, rfl⟩, y, hy, rfl⟩ := Subgroup.mem_sup.mp
      (show x ∈ (diagonal K).range ⊔ supportedIdeles (K := K) S by rw [hS]; exact Subgroup.mem_top x)
    rw [map_mul, map_mul, toFractionalIdeal_diagonal,
      artinMap_principal_eq_one_of_split_real G hu hr, _root_.one_mul]
    apply Subgroup.mem_bot.mp
    refine primeValuesHom_mem ⊥ _ fun v hv => Subgroup.mem_bot.mpr ?_
    rw [frobeniusOrOne, if_pos (hu v)]
    exact hf v (not_not.mp fun hn => hv (by rw [count_toFractionalIdeal]; exact hy v hn))
  let M : Modulus K := ⟨⊤, top_ne_bot, Set.univ⟩
  have surj := MonoidHom.range_eq_top.mp
    (range_artinMap_comp_subtype K L G M (fun v _ => hu v))
  refine ⟨fun x y => ?_⟩
  obtain ⟨I, rfl⟩ := surj x
  obtain ⟨J, rfl⟩ := surj y
  exact (hall I.val).trans (hall J.val).symm

end GlobalTheory.Reciprocity
