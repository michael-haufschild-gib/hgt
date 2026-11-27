import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleRayCongruence
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.MultiplicativeWeakApproximation

/-! Weak approximation supplies a diagonal multiplier satisfying the
finite and infinite congruence conditions of any ray. -/

noncomputable section

open Topology Filter NumberField IsDedekindDomain GaloisForLFunctions.HeckeLFunctions

namespace GlobalTheory.Reciprocity.IdeleRay

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

theorem exists_diagonal_mul_mem_idelesOneMod (x : IdeleGroup K) :
    ∃ a : Kˣ, diagonal K a * x ∈ idelesOneMod 𝔪 := by
  classical
  let S : Finset (HeightOneSpectrum (𝓞 K)) := (finite_primes_dvd 𝔪).toFinset
  let T : Finset (InfinitePlace K) := Finset.univ
  let O : Set (((v : S) → (v.1.adicCompletion K)ˣ) × ((w : T) → (w.1.Completion)ˣ)) :=
    (Set.univ.pi fun v : S ↦ {z | z * finiteProj v.1 x ∈ unitsLevel v.1 (exponent 𝔪 v.1)}) ×ˢ
      (Set.univ.pi fun w : T ↦ {z | ∀ hw : w.1.IsReal,
        (⟨w.1, hw⟩ : {w : InfinitePlace K // w.IsReal}) ∈ 𝔪.inf →
          0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
            ((z * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)})
  have hO : IsOpen O := by
    refine (isOpen_set_pi Set.finite_univ fun v _ ↦ ?_).prod
      (isOpen_set_pi Set.finite_univ fun w _ ↦ ?_)
    · exact (isOpen_unitsLevel v.1 _).preimage (continuous_mul_const _)
    · simp only [Set.setOf_forall]
      refine isOpen_iInter_of_finite fun hw ↦ isOpen_iInter_of_finite fun _ ↦ ?_
      exact isOpen_lt continuous_const
        ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous.comp
          (Units.continuous_val.comp (continuous_mul_const _)))
  have hne : O.Nonempty := by
    refine ⟨(fun v ↦ (finiteProj v.1 x)⁻¹, fun w ↦ (infiniteProj w.1 x)⁻¹),
      Set.mem_univ_pi.2 fun v ↦ ?_, Set.mem_univ_pi.2 fun w ↦ ?_⟩
    · show (finiteProj v.1 x)⁻¹ * finiteProj v.1 x ∈ unitsLevel v.1 (exponent 𝔪 v.1)
      rw [inv_mul_cancel]
      exact one_mem _
    · intro hw _
      show 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((infiniteProj w.1 x)⁻¹ * infiniteProj w.1 x : (w.1.Completion)ˣ) : w.1.Completion)
      rw [inv_mul_cancel, Units.val_one, map_one]
      exact one_pos
  obtain ⟨a, ha⟩ := (denseRange_units_prod_pi S T).exists_mem_open hO hne
  refine ⟨a, (mem_idelesOneMod 𝔪).2 ⟨fun v hv ↦ ?_, fun w hw ↦ ?_⟩⟩
  · have hvS : v ∈ S := by
      exact (finite_primes_dvd 𝔪).mem_toFinset.mpr hv
    have h := Set.mem_univ_pi.1 ha.1 ⟨v, hvS⟩
    have he : finiteProj v (diagonal K a) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
      refine Units.ext ?_
      change ((a : K) : v.adicCompletion K) = algebraMap K (v.adicCompletion K) a
      rw [HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [map_mul, he]
    exact h
  · have h := Set.mem_univ_pi.1 ha.2 ⟨w.1, Finset.mem_univ _⟩ w.2 hw
    have he : infiniteProj w.1 (diagonal K a) =
        Units.map (algebraMap K w.1.Completion).toMonoidHom a :=
      Units.ext rfl
    rw [map_mul, he]
    exact h

end GlobalTheory.Reciprocity.IdeleRay
