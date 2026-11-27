import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.SUnitLocalPowers
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PowerCongruenceIndex

/-! The index of the image of the local power subgroup is the degree
of the S-unit radical extension. Hence the local powers and the diagonal
generate the kernel of its Artin map. -/

noncomputable section

open NumberField IsDedekindDomain FractionalIdeal IntermediateField GaloisForLFunctions
open GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative nonZeroDivisors

namespace GlobalTheory.Kummer

open GlobalTheory.Reciprocity GlobalTheory.Reciprocity.IdeleGroup GlobalTheory.Reciprocity.IdeleRay

variable {K : Type} [Field K] [NumberField K]

private theorem ord_diagonal_eq_ordAt (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ord v (diagonal K a) = ordAt K v (Additive.ofMul a) := by
  have h := toFractionalIdeal_eq_iff.mp (toFractionalIdeal_diagonal (K := K) a) v
  rwa [GaloisForLFunctions.count_toPrincipalIdeal] at h

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "D" => (MonoidHom.range (diagonal K))
local notation "J" => supportedIdeles (K := K) (S : Set _)
local notation "U" => (Multiplicative (sUnits K Gal(K/K) (sUnitPrimeSet K S)))

private def unitValue : U →* Kˣ :=
  (sUnits K Gal(K/K) (sUnitPrimeSet K S)).subtype.toMultiplicative

private def unitToIdele : U →* J :=
  ((diagonal K).comp (unitValue S)).codRestrict _ fun u v hv => by
    change ord v (diagonal K (unitValue S u)) = 0
    rw [ord_diagonal_eq_ordAt]
    exact (Multiplicative.toAdd u).2 v hv

variable (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]

local notation "P" => powerCongruence (K := K) n S

private theorem comap_powerCongruence
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : D ⊔ J = ⊤) :
    ((P).subgroupOf J).comap (unitToIdele S) = (powMonoidHom n : U →* U).range := by
  ext u
  let a := unitValue S u
  change diagonal K a ∈ P ↔ u ∈ (powMonoidHom n : U →* U).range
  constructor
  · rintro ⟨hf, hi, -⟩
    obtain ⟨r, hr⟩ := exists_pow_eq_of_local_sUnit S hnS hJ (Multiplicative.toAdd u).2
      (fun v hv => by
        obtain ⟨b, hb⟩ := hf v hv
        exact ⟨(b : v.adicCompletion K), by
          change (b : v.adicCompletion K) ^ n = ((a : K) : v.adicCompletion K)
          rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hb, coe_finiteProj_diagonal]⟩)
      (fun w => by
        obtain ⟨b, hb⟩ := hi w
        exact ⟨(b : w.Completion), by
          change (b : w.Completion) ^ n = ((a : K) : w.Completion)
          rw [← Units.val_pow_eq_pow_val, ← powMonoidHom_apply, hb, coe_infiniteProj_diagonal]⟩)
    have hr0 : r ≠ 0 := by
      intro h
      rw [h, zero_pow (NeZero.ne n)] at hr
      exact a.ne_zero hr.symm
    let b := Units.mk0 r hr0
    have hb : b ^ n = a := Units.ext hr
    have hbu : Additive.ofMul b ∈ sUnits K Gal(K/K) (sUnitPrimeSet K S) :=
      (nsmul_mem_sUnits_iff K Gal(K/K) (sUnitPrimeSet K S) (NeZero.ne n)).mp
        (show Additive.ofMul (b ^ n) ∈ _ from hb ▸ (Multiplicative.toAdd u).2)
    exact ⟨Multiplicative.ofAdd ⟨Additive.ofMul b, hbu⟩, Subtype.ext hb⟩
  · rintro ⟨b, rfl⟩
    refine ⟨?_, ?_, (unitToIdele S (b ^ n)).2⟩
    · intro v _
      exact ⟨finiteProj v (diagonal K (unitValue S b)), by
        change (finiteProj v (diagonal K (unitValue S b))) ^ n =
          finiteProj v (diagonal K (unitValue S (b ^ n)))
        rw [← map_pow, ← map_pow, ← map_pow]⟩
    · intro w
      exact ⟨infiniteProj w (diagonal K (unitValue S b)), by
        change (infiniteProj w (diagonal K (unitValue S b))) ^ n =
          infiniteProj w (diagonal K (unitValue S (b ^ n)))
        rw [← map_pow, ← map_pow, ← map_pow]⟩

private theorem index_sup_powerCongruence
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : D ⊔ J = ⊤) :
    (D ⊔ P).index = n ^ (Fintype.card (InfinitePlace K) + S.card) := by
  let C := IdeleGroup K ⧸ D
  let q : IdeleGroup K →* C := QuotientGroup.mk' D
  let f := q.comp (J).subtype
  let W := (P).subgroupOf J
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D x
    obtain ⟨d, hd, z, hz, rfl⟩ := Subgroup.mem_sup.mp
      (show y ∈ D ⊔ J by rw [hJ]; exact Subgroup.mem_top y)
    exact ⟨⟨z, hz⟩, by
      change q z = q (d * z)
      have he : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
      rw [map_mul, he]
      exact (_root_.one_mul (q z)).symm⟩
  have hker : (unitToIdele S).range = f.ker := by
    ext x
    change (∃ a : U, unitToIdele S a = x) ↔ q x.val = 1
    refine Iff.trans ?_ ((QuotientGroup.eq_one_iff (N := D) x.val).symm)
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨unitValue S a, rfl⟩
    · rintro ⟨a, ha⟩
      have h : Additive.ofMul a ∈ sUnits K Gal(K/K) (sUnitPrimeSet K S) := by
        intro v hv
        rw [← ord_diagonal_eq_ordAt, ha]
        exact x.2 v hv
      exact ⟨Multiplicative.ofAdd ⟨Additive.ofMul a, h⟩, Subtype.ext ha⟩
  have hmap : W.map f = (P).map q := by
    rw [show f = q.comp (J).subtype from rfl, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (show P ≤ J from fun _ hx => hx.2.2)]
  have hmapIndex : ((P).map q).index = (D ⊔ P).index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk', (q.range_eq_top_of_surjective
      (QuotientGroup.mk'_surjective D)), Subgroup.index_top, mul_one, sup_comm]
  have hW : W.index = n ^ (2 * (Fintype.card (InfinitePlace K) + S.card)) :=
    relIndex_powerCongruence_eq_pow n S hnS
  have hU : (W.comap (unitToIdele S)).index = n ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [comap_powerCongruence S n hnS hJ, index_power_sUnits, card_sUnitPrimeSet]
  have h : (W.map f).index * (W.comap (unitToIdele S)).index = W.index := by
    rw [Subgroup.index_comap, hker, Subgroup.index_map, f.range_eq_top_of_surjective hsurj,
      Subgroup.index_top, mul_one, ← Subgroup.relIndex_sup_left, mul_comm]
    exact Subgroup.relIndex_mul_index le_sup_left
  let k := Fintype.card (InfinitePlace K) + S.card
  rw [hmap, hmapIndex, hU, hW] at h
  change (D ⊔ P).index * n ^ k = n ^ (2 * k) at h
  rw [two_mul, pow_add n k k] at h
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) k) h

local notation "M" => sUnitRadicalExtension K S n

theorem exists_sUnitRadical_artin_exact
    (hnS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hJ : D ⊔ J = ⊤) :
    letI : Fintype Gal(M/K) := Fintype.ofFinite _
    letI : NumberField M := NumberField.of_module_finite K M
    letI : CommGroup Gal(M/K) :=
      { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }
    ∃ (m : Modulus K) (a : IdeleGroup K →* Gal(M/K)), Continuous a ∧ Function.Surjective a ∧
      a.ker = D ⊔ P ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ m.fin ↔ ¬ IsUnramifiedPrime K M Gal(M/K) v) ∧
      ∀ x : idelesOneMod m, a x.val = artinMap K M Gal(M/K) (toFractionalIdeal x.val) := by
  letI : Fintype Gal(M/K) := Fintype.ofFinite _
  letI : NumberField M := NumberField.of_module_finite K M
  letI : CommGroup Gal(M/K) :=
    { (inferInstance : Group Gal(M/K)) with mul_comm := IsMulCommutative.is_comm.comm }
  obtain ⟨m, a, hc, hs, hle, hm, ha⟩ := exists_sUnitRadical_artin K S n hnS
  refine ⟨m, a, hc, hs, le_antisymm ?_ hle, hm, ha⟩
  have hcard : a.ker.index = n ^ (Fintype.card (InfinitePlace K) + S.card) := by
    rw [Subgroup.index_ker, a.range_eq_top_of_surjective hs]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).trans
      ((IsGalois.card_aut_eq_finrank K M).trans (finrank_sUnitRadicalExtension K S n))
  have hr := Subgroup.relIndex_mul_index hle
  rw [hcard, index_sup_powerCongruence S n hnS hJ] at hr
  exact Subgroup.relIndex_eq_one.mp
    (Nat.eq_of_mul_eq_mul_right (pow_pos (NeZero.pos n) _) (hr.trans (one_mul _).symm))

end GlobalTheory.Kummer
