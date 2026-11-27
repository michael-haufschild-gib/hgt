import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdelicRayClass
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.IdeleRestrictedProduct

/-! An idelic ray map has open kernel. Local congruences are open
conditions at finitely many places and integral units form an open
subgroup of the restricted product. -/

noncomputable section

open Filter Topology NumberField IsDedekindDomain FractionalIdeal
open GaloisForLFunctions.HeckeLFunctions
open scoped RestrictedProduct

namespace GlobalTheory.Reciprocity.IdeleRay

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

theorem isOpen_idelesOneMod : IsOpen (idelesOneMod 𝔪 : Set (IdeleGroup K)) := by
  have h : (idelesOneMod 𝔪 : Set (IdeleGroup K)) =
      (⋂ v ∈ {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔪.fin},
        (finiteProj v) ⁻¹' (unitsLevel (K := K) v (exponent 𝔪 v) : Set (v.adicCompletion K)ˣ)) ∩ positiveAt 𝔪.inf := by
    ext x
    simp only [SetLike.mem_coe, mem_idelesOneMod, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.mem_preimage, mem_positiveAt]
  rw [h]
  exact ((finite_primes_dvd 𝔪).isOpen_biInter fun v _ =>
    (isOpen_unitsLevel v _).preimage (continuous_finiteProj v)).inter (isOpen_positiveAt 𝔪.inf)

theorem isOpen_ker_toFractionalIdeal :
    IsOpen ((toFractionalIdeal (K := K)).ker : Set (IdeleGroup K)) := by
  let R (v : HeightOneSpectrum (𝓞 K)) := (v.adicCompletion K)ˣ
  let A (v : HeightOneSpectrum (𝓞 K)) := (Submonoid.ofClass (v.adicCompletionIntegers K)).units
  let V : Set (Πʳ v, [R v, A v]) := {y | ∀ v, y v ∈ A v}
  have hV : IsOpen V := _root_.RestrictedProduct.isOpen_forall_mem
    (A := fun v => (A v : Set (R v))) (isOpen_units_adicCompletionIntegers K)
  let e := fun x : IdeleGroup K => (prodRestrictedEquiv K x).2
  have he : Continuous e := continuous_snd.comp (prodRestrictedEquiv K).continuous
  have hEq : (toFractionalIdeal (K := K)).ker = {x | e x ∈ V} := by
    ext x
    change toFractionalIdeal x = 1 ↔ ∀ v, e x v ∈ A v
    simp only [toFractionalIdeal_eq_iff, Units.val_one, count_one]
    refine forall_congr' fun v => ?_
    have hval : e x v = finiteProj v x := Units.ext rfl
    rw [ord_eq_zero_iff, hval, Submonoid.mem_units_iff, coe_finiteProj,
      ← map_inv, coe_finiteProj]
    rfl
  exact hEq.symm ▸ hV.preimage he

theorem isOpen_ker_toRayClass : IsOpen ((toRayClass 𝔪).ker : Set (IdeleGroup K)) := by
  let W := (idelesOneMod 𝔪 : Set (IdeleGroup K)) ∩ (toFractionalIdeal (K := K)).ker
  have hW : IsOpen W := (isOpen_idelesOneMod 𝔪).inter (isOpen_ker_toFractionalIdeal (K := K))
  have hW1 : (1 : IdeleGroup K) ∈ W := ⟨one_mem _, one_mem _⟩
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hW.mem_nhds hW1) ?_)
  intro x hx
  have h := toRayClass_normalized 𝔪 1 ⟨x, hx.1⟩
  simp only [map_one, one_mul] at h
  change toRayClass 𝔪 x = 1
  rw [h, show toCoprimeIdeals 𝔪 ⟨x, hx.1⟩ = 1 from Subtype.ext hx.2, map_one]

theorem continuous_toRayClass [TopologicalSpace (RayClassGroup 𝔪)]
    [DiscreteTopology (RayClassGroup 𝔪)] : Continuous (toRayClass 𝔪) := by
  apply continuous_of_continuousAt_one (toRayClass 𝔪)
  rw [ContinuousAt, nhds_discrete (RayClassGroup 𝔪), map_one, tendsto_pure]
  exact (isOpen_ker_toRayClass 𝔪).mem_nhds (map_one _)

end GlobalTheory.Reciprocity.IdeleRay
