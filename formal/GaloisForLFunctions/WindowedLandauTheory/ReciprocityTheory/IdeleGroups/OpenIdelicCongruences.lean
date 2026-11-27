import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.CompactIdelicClassQuotient
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitNeighborhoods
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.PowerCongruenceIdeles

/-! An open subgroup of the compact idelic quotient contains a
congruence neighbourhood specified by finitely many local levels. -/

noncomputable section

open Topology Filter NumberField IsDedekindDomain

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

theorem exists_finite_congruences_le_open
    (H : Subgroup (CompactIdeleClassQuotient K)) (hH : IsOpen (H : Set (CompactIdeleClassQuotient K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (n : S → ℕ), ∀ x : IdeleGroup K,
      (∀ v, ord v x = 0) → x ∈ positiveAt Set.univ →
      (∀ v : S, finiteProj v.val x ∈ unitsLevel v.val (n v)) →
        toCompactIdeleClassQuotient K x ∈ H := by
  classical
  let q := toCompactIdeleClassQuotient K
  have hq : Continuous q := QuotientGroup.continuous_mk
  let V : Set (FiniteIntegralUnits K) := (q ∘ finiteIntegralIdele) ⁻¹' (H : Set _)
  have hVopen : IsOpen V := hH.preimage (hq.comp continuous_finiteIntegralIdele)
  have hVone : (1 : FiniteIntegralUnits K) ∈ V := by
    change q (finiteIntegralIdele 1) ∈ H
    rw [show (finiteIntegralIdele (1 : FiniteIntegralUnits K)) = 1 by
      change (prodRestrictedEquiv K).symm 1 = 1
      exact map_one _]
    exact H.one_mem
  have hV := hVopen.mem_nhds hVone
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨S, U, hU, hsub⟩ := hV
  have hx (v : S) : ∃ n, ∀ a : (Submonoid.ofClass (v.val.adicCompletionIntegers K)).units,
      (a : (v.val.adicCompletion K)ˣ) ∈ unitsLevel v.val n → a ∈ U v := by
    have h := hU (v : HeightOneSpectrum (𝓞 K))
    rw [IsEmbedding.subtypeVal.nhds_eq_comap, Filter.mem_comap] at h
    obtain ⟨T, hT, hTU⟩ := h
    obtain ⟨n, -, hn⟩ := exists_unitsLevel_subset v.val hT
    exact ⟨n, fun a ha => hTU (hn ha)⟩
  choose n hn using hx
  refine ⟨S, n, fun x hx hpos hlevel => ?_⟩
  obtain ⟨a, ha⟩ := exists_finiteIntegralUnits_of_ord_zero hx
  have hqa : q (finiteIntegralIdele a) ∈ H :=
    hsub fun v hv => hn ⟨v, hv⟩ (a v) (by
      rw [← finiteProj_finiteIntegralIdele, ← ha v]
      exact hlevel ⟨v, hv⟩)
  let y := x * (finiteIntegralIdele a)⁻¹
  have hy : y ∈ archPositive K := by
    refine ⟨MonoidHom.mem_ker.mpr ?_, mem_positiveAt.mpr fun w hw => ?_⟩
    · exact toFinite_eq_one_of_finiteProj (fun v => by simp [y, ← ha v])
    · simpa only [y, map_mul, map_inv, infiniteProj_finiteIntegralIdele, inv_one, mul_one]
        using (mem_positiveAt.mp hpos) w hw
  have he : q y = 1 := toCompactIdeleClassQuotient_of_archPositive K hy
  change q x * (q (finiteIntegralIdele a))⁻¹ = 1 at he
  rwa [mul_inv_eq_one.mp he]

theorem exists_powerCongruence_map_le_open
    (H : Subgroup (CompactIdeleClassQuotient K)) (hH : IsOpen (H : Set (CompactIdeleClassQuotient K)))
    {n : ℕ} (hpow : ∀ c : CompactIdeleClassQuotient K, c ^ n ∈ H)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), T ⊆ S ∧
      (powerCongruence n S).map (toCompactIdeleClassQuotient K) ≤ H := by
  classical
  obtain ⟨S₀, m, hm⟩ := exists_finite_congruences_le_open H hH
  refine ⟨T ∪ S₀, Finset.subset_union_left, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, z, rfl, hfin, hinf, hord⟩ := exists_normalized_of_mem_powerCongruence hx
  rw [map_mul, map_pow]
  refine H.mul_mem (hpow _) (hm z hord ?_ fun v => ?_)
  · refine mem_positiveAt.mpr fun w _ => ?_
    simp [hinf w.val]
  · rw [hfin v.val (Finset.mem_union_right _ v.2)]
    exact one_mem _

end GlobalTheory.Reciprocity
