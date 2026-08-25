import GaloisForLFunctions.HTGeometry.ABHN.CanonicalNonarchimedeanLocalBrauerFinite

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued

set_option maxHeartbeats 2000000

/-- Frobenius-normalized invariant on the directed supremum of factorial Brauer slices. -/
noncomputable def canonicalNonarchimedeanLocalBrauerISupInvariant
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ↥(⨆ n, localBrauerFactorialSlice K n) →+ RatModInt :=
  addSubgroupISupLift (localBrauerFactorialSlice K)
    (localBrauerFactorialSlices_directed K)
    (localBrauerFactorialFrobeniusInvariant K)
    (localBrauerFactorialFrobeniusInvariants_agree K)

/-- Canonical arithmetic-Frobenius invariant on the full Brauer group of a nonarchimedean local
field, glued from the exhaustive factorial unramified tower. -/
noncomputable def canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    BrauerGroup K →+ RatModInt :=
  addSubgroupISupLiftOfTop (localBrauerFactorialSlice K)
    (localBrauerFactorialSlices_directed K)
    (localBrauerFactorialFrobeniusInvariant K)
    (localBrauerFactorialFrobeniusInvariants_agree K) hTop

theorem canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_apply_stage
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) (n : ℕ)
    (x : localBrauerFactorialSlice K n) :
    canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion K hTop
        (x : BrauerGroup K) =
      localBrauerFactorialFrobeniusInvariant K n x := by
  exact addSubgroupISupLiftOfTop_apply_mem
    (localBrauerFactorialSlice K) (localBrauerFactorialSlices_directed K)
    (localBrauerFactorialFrobeniusInvariant K)
    (localBrauerFactorialFrobeniusInvariants_agree K) hTop n x

theorem localBrauerFactorialFrobeniusInvariant_injective
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Function.Injective (localBrauerFactorialFrobeniusInvariant K n) := by
  let D := localBrauerFactorialRootLift K n
  exact (zmodRatModIntAddHom_injective D.polynomial.natDegree
    D.natDegree_ne_zero).comp D.cyclicBrauerFrobeniusInvariantOverBase.injective

theorem canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_injective
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    Function.Injective
      (canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion K hTop) := by
  intro x y hxy
  have hmem : x - y ∈ ⨆ n, localBrauerFactorialSlice K n := by
    rw [hTop]
    exact AddSubgroup.mem_top _
  obtain ⟨n, hn⟩ :=
    (AddSubgroup.mem_iSup_of_directed (localBrauerFactorialSlices_directed K)).mp hmem
  let z : localBrauerFactorialSlice K n := ⟨x - y, hn⟩
  have hzglobal : canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion K hTop
      (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzstage : localBrauerFactorialFrobeniusInvariant K n z = 0 := by
    rw [← canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_apply_stage
      K hTop n z]
    exact hzglobal
  have hz : z = 0 := localBrauerFactorialFrobeniusInvariant_injective K n
    (hzstage.trans (map_zero _).symm)
  apply sub_eq_zero.mp
  exact congrArg Subtype.val hz

theorem canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_surjective
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    Function.Surjective
      (canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion K hTop) := by
  intro q
  obtain ⟨d, hd, hqd⟩ := ratModInt_exists_nonzero_nsmul_eq_zero q
  have hdiv : d ∣ localBrauerFactorialDegree d := by
    change d ∣ (d + 1).factorial
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hd) (Nat.le_add_right d 1)
  let D := localBrauerFactorialRootLift K d
  have hqD : q ∈ ratModIntNTorsion D.polynomial.natDegree := by
    rw [localBrauerFactorialRootLift_natDegree K d]
    exact ratModIntNTorsion_mono hdiv hqd
  have hqrange : q ∈ (zmodRatModIntAddHom D.polynomial.natDegree
      D.natDegree_ne_zero).range := by
    rw [zmodRatModIntAddHom_range_eq_ratModIntNTorsion]
    exact hqD
  obtain ⟨z, hz⟩ := hqrange
  let x := D.cyclicBrauerFrobeniusInvariantOverBase.symm z
  refine ⟨(x : BrauerGroup K), ?_⟩
  rw [canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_apply_stage
    K hTop d x]
  change zmodRatModIntAddHom D.polynomial.natDegree D.natDegree_ne_zero
    (D.cyclicBrauerFrobeniusInvariantOverBase x) = q
  rw [D.cyclicBrauerFrobeniusInvariantOverBase.apply_symm_apply]
  exact hz

/-- Full arithmetic-Frobenius-normalized local invariant, assuming factorial unramified
exhaustion. -/
noncomputable def canonicalLocalBrauerGroupAddEquivRatModIntOfFactorialExhaustion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    BrauerGroup K ≃+ RatModInt :=
  AddEquiv.ofBijective
    (canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion K hTop)
    ⟨canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_injective K hTop,
      canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_surjective K hTop⟩

theorem canonicalLocalBrauerGroupAddEquivRatModIntOfFactorialExhaustion_apply_stage
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) (n : ℕ)
    (x : localBrauerFactorialSlice K n) :
    canonicalLocalBrauerGroupAddEquivRatModIntOfFactorialExhaustion K hTop
        (x : BrauerGroup K) =
      localBrauerFactorialFrobeniusInvariant K n x := by
  exact canonicalNonarchimedeanLocalBrauerInvariantOfFactorialExhaustion_apply_stage
    K hTop n x

/-- Canonical arithmetic-Frobenius/Hasse invariant for every nonarchimedean local field in its
normed-field presentation. -/
noncomputable def canonicalNonarchimedeanLocalBrauerGroupAddEquivRatModInt
    (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [IsUltrametricDist F] [LocallyCompactSpace F] :
    BrauerGroup F ≃+ RatModInt := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  exact canonicalLocalBrauerGroupAddEquivRatModIntOfFactorialExhaustion F
    (iSup_localBrauerFactorialSlice_eq_top F)

/-- Canonical arithmetic-Frobenius/Hasse invariant `Br(ℚₚ) ≃ ℚ/ℤ`. -/
noncomputable def canonicalPadicBrauerGroupAddEquivRatModInt
    (p : ℕ) [Fact p.Prime] : BrauerGroup ℚ_[p] ≃+ RatModInt :=
  canonicalNonarchimedeanLocalBrauerGroupAddEquivRatModInt ℚ_[p]

end
end GaloisForLFunctions.HTGeometry.ABHN
