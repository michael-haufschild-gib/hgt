import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.PowerCongruenceIdeles
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelesWithFiniteSupport
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalPowerIndexProducts

/-! The relative index of simultaneous local power conditions is the
product of the power indices at the specified places. -/

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Reciprocity.IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

private def localProjections (S : Finset (HeightOneSpectrum (𝓞 K))) :
    supportedIdeles (K := K) (S : Set (HeightOneSpectrum (𝓞 K))) →*
      ((∀ v : S, (v.val.adicCompletion K)ˣ) × (∀ w : InfinitePlace K, (w.Completion)ˣ)) :=
  ((MonoidHom.pi fun v : S => finiteProj v.val).prod
    (MonoidHom.pi fun w : InfinitePlace K => infiniteProj w)).comp (supportedIdeles (K := K) (S : Set (HeightOneSpectrum (𝓞 K)))).subtype

private theorem localProjections_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (localProjections S) := by
  rintro ⟨a, b⟩
  obtain ⟨y, hfin, hinf, hout⟩ := exists_with_local_coordinates S a b
  have hy : y ∈ supportedIdeles (K := K) (S : Set (HeightOneSpectrum (𝓞 K))) := fun v hv => by
    rw [ord, ← coe_finiteProj, hout v hv, Units.val_one, map_one, WithZero.log_one, neg_zero]
  exact ⟨⟨y, hy⟩, Prod.ext (funext hfin) (funext hinf)⟩

theorem relIndex_powerCongruence (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerCongruence n S).relIndex (supportedIdeles (K := K) (S : Set (HeightOneSpectrum (𝓞 K)))) =
      (∏ v : S, (powMonoidHom n : (v.val.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by
  let f := localProjections S
  let G := (∀ v : S, (v.val.adicCompletion K)ˣ) × (∀ w : InfinitePlace K, (w.Completion)ˣ)
  let P := (powMonoidHom n : G →* G).range
  have he : (powerCongruence n S).subgroupOf (supportedIdeles (K := K) (S : Set (HeightOneSpectrum (𝓞 K)))) = P.comap f := by
    ext x
    change ((∀ v ∈ S, finiteProj v x.val ∈ (powMonoidHom n).range) ∧
      (∀ w : InfinitePlace K, infiniteProj w x.val ∈ (powMonoidHom n).range) ∧
      ∀ v ∉ S, ord v x.val = 0) ↔ ∃ y : G, y ^ n = f x
    constructor
    · rintro ⟨hf, hi, -⟩
      choose a ha using fun v : S => hf v.val v.2
      choose b hb using hi
      exact ⟨⟨a, b⟩, Prod.ext (funext ha) (funext hb)⟩
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨fun v hv => ⟨a ⟨v, hv⟩, congrFun (congrArg Prod.fst h) ⟨v, hv⟩⟩,
        fun w => ⟨b w, congrFun (congrArg Prod.snd h) w⟩, x.2⟩
  rw [Subgroup.relIndex, he]
  have hf : Function.Surjective f := localProjections_surjective S
  exact (P.index_comap_of_surjective hf).trans
    ((index_power_prod n).trans (congrArg₂ (· * ·) (index_power_pi n) (index_power_pi n)))

end GlobalTheory.Reciprocity.IdeleGroup
