/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalBrauerCompatibleCoordinates
import Mathlib.Data.Set.UnionLift

/-!
# Nonarchimedean local Brauer invariant

Compatible finite invariants on the exhaustive factorial tower glue to an additive equivalence
from the Brauer group of a nonarchimedean local field to `ℚ/ℤ`.  Injectivity uses source-side
factorial exhaustion; surjectivity uses target-side finite-torsion exhaustion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued

noncomputable def localBrauerFactorialInvariant
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    localBrauerFactorialSlice K n →+ RatModInt :=
  (zmodRatModIntAddHom (localBrauerFactorialDegree n)
    (localBrauerFactorialDegree_ne_zero n)).comp
      (localBrauerFactorialCompatibleAddEquiv K n).symm.toAddMonoidHom

theorem localBrauerFactorialInvariant_inclusion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {m n : ℕ} (hmn : m ≤ n)
    (x : localBrauerFactorialSlice K m) :
    localBrauerFactorialInvariant K n
        (localBrauerFactorialInclusion K hmn x) =
      localBrauerFactorialInvariant K m x := by
  obtain ⟨z, rfl⟩ := (localBrauerFactorialCompatibleAddEquiv K m).surjective x
  dsimp only [localBrauerFactorialInvariant, AddMonoidHom.comp_apply]
  change zmodRatModIntAddHom (localBrauerFactorialDegree n)
      (localBrauerFactorialDegree_ne_zero n)
      ((localBrauerFactorialCompatibleAddEquiv K n).symm
        (localBrauerFactorialInclusion K hmn
          (localBrauerFactorialCompatibleAddEquiv K m z))) =
    zmodRatModIntAddHom (localBrauerFactorialDegree m)
      (localBrauerFactorialDegree_ne_zero m)
      ((localBrauerFactorialCompatibleAddEquiv K m).symm
        (localBrauerFactorialCompatibleAddEquiv K m z))
  rw [(localBrauerFactorialCompatibleAddEquiv K m).symm_apply_apply]
  rw [show (localBrauerFactorialCompatibleAddEquiv K n).symm
      (localBrauerFactorialInclusion K hmn
        (localBrauerFactorialCompatibleAddEquiv K m z)) =
      localBrauerFactorialTransition hmn z by
      apply (localBrauerFactorialCompatibleAddEquiv K n).injective
      rw [(localBrauerFactorialCompatibleAddEquiv K n).apply_symm_apply]
      exact localBrauerFactorialCompatibleAddEquiv_of_le K hmn z]
  exact zmodRatModIntAddHom_transition
    (localBrauerFactorialDegree_ne_zero m)
    (localBrauerFactorialDegree_ne_zero n)
    (localBrauerFactorialDegree_dvd_of_le hmn) z

noncomputable def addSubgroupISupLift
    {A B ι : Type*} [AddGroup A] [AddGroup B] [Nonempty ι]
    (S : ι → AddSubgroup A) (dir : Directed (· ≤ ·) S)
    (f : ∀ i, S i →+ B)
    (compat : ∀ (i j : ι) (x : A) (hxi : x ∈ S i) (hxj : x ∈ S j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩) :
    ↥(⨆ i, S i) →+ B := by
  exact {
    toFun := Set.iUnionLift (fun i => (S i : Set A)) (fun i x => f i x) compat
      (((⨆ i, S i) : AddSubgroup A) : Set A)
      (le_of_eq (AddSubgroup.coe_iSup_of_directed dir))
    map_zero' := by
      dsimp
      exact Set.iUnionLift_const _ (fun i : ι => (0 : S i)) (fun _ => rfl) _ (by simp)
    map_add' := by
      dsimp
      apply Set.iUnionLift_binary (AddSubgroup.coe_iSup_of_directed dir) dir _
        (fun _ => (· + ·))
      all_goals simp }

@[simp] theorem addSubgroupISupLift_inclusion
    {A B ι : Type*} [AddGroup A] [AddGroup B] [Nonempty ι]
    {S : ι → AddSubgroup A} {dir : Directed (· ≤ ·) S}
    {f : ∀ i, S i →+ B}
    {compat : ∀ (i j : ι) (x : A) (hxi : x ∈ S i) (hxj : x ∈ S j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩}
    {i : ι} (x : S i) :
    addSubgroupISupLift S dir f compat
        (AddSubgroup.inclusion (le_iSup S i) x) = f i x := by
  change Set.iUnionLift (fun i => (S i : Set A)) (fun i x => f i x) compat
      (((⨆ i, S i) : AddSubgroup A) : Set A)
      (le_of_eq (AddSubgroup.coe_iSup_of_directed dir))
      (AddSubgroup.inclusion (le_iSup S i) x) = f i x
  have h := Set.iUnionLift_of_mem
      (S := fun i => (S i : Set A)) (f := fun i x => f i x) (hf := compat)
      (T := (((⨆ i, S i) : AddSubgroup A) : Set A))
      (hT := le_of_eq (AddSubgroup.coe_iSup_of_directed dir))
      (AddSubgroup.inclusion (le_iSup S i) x) x.property
  exact h.trans (congrArg (f i) (Subtype.ext rfl))

noncomputable def addSubgroupISupLiftOfTop
    {A B ι : Type*} [AddGroup A] [AddGroup B] [Nonempty ι]
    (S : ι → AddSubgroup A) (dir : Directed (· ≤ ·) S)
    (f : ∀ i, S i →+ B)
    (compat : ∀ (i j : ι) (x : A) (hxi : x ∈ S i) (hxj : x ∈ S j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hTop : ⨆ i, S i = ⊤) : A →+ B :=
  (addSubgroupISupLift S dir f compat).comp
    ((AddSubgroup.inclusion (show (⊤ : AddSubgroup A) ≤ ⨆ i, S i by rw [hTop])).comp
      AddSubgroup.topEquiv.symm.toAddMonoidHom)

theorem addSubgroupISupLiftOfTop_apply_mem
    {A B ι : Type*} [AddGroup A] [AddGroup B] [Nonempty ι]
    (S : ι → AddSubgroup A) (dir : Directed (· ≤ ·) S)
    (f : ∀ i, S i →+ B)
    (compat : ∀ (i j : ι) (x : A) (hxi : x ∈ S i) (hxj : x ∈ S j),
      f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (hTop : ⨆ i, S i = ⊤) (i : ι) (x : S i) :
    addSubgroupISupLiftOfTop S dir f compat hTop (x : A) = f i x := by
  change addSubgroupISupLift S dir f compat
      ((AddSubgroup.inclusion (show (⊤ : AddSubgroup A) ≤ ⨆ i, S i by rw [hTop]))
        (AddSubgroup.topEquiv.symm (x : A))) = _
  rw [show (AddSubgroup.inclusion (show (⊤ : AddSubgroup A) ≤ ⨆ i, S i by rw [hTop]))
      (AddSubgroup.topEquiv.symm (x : A)) =
      AddSubgroup.inclusion (le_iSup S i) x by
        apply Subtype.ext
        rfl]
  exact addSubgroupISupLift_inclusion x

theorem localBrauerFactorialSlices_directed
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Directed (· ≤ ·) (localBrauerFactorialSlice K) := by
  intro m n
  exact ⟨max m n, localBrauerFactorialSlice_mono K (Nat.le_max_left m n),
    localBrauerFactorialSlice_mono K (Nat.le_max_right m n)⟩

theorem localBrauerFactorialInvariants_agree
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m n : ℕ) (x : BrauerGroup K)
    (hxm : x ∈ localBrauerFactorialSlice K m)
    (hxn : x ∈ localBrauerFactorialSlice K n) :
    localBrauerFactorialInvariant K m ⟨x, hxm⟩ =
      localBrauerFactorialInvariant K n ⟨x, hxn⟩ := by
  let k := max m n
  calc
    localBrauerFactorialInvariant K m ⟨x, hxm⟩ =
        localBrauerFactorialInvariant K k
          (localBrauerFactorialInclusion K (Nat.le_max_left m n) ⟨x, hxm⟩) :=
      (localBrauerFactorialInvariant_inclusion K (Nat.le_max_left m n) ⟨x, hxm⟩).symm
    _ = localBrauerFactorialInvariant K k
          (localBrauerFactorialInclusion K (Nat.le_max_right m n) ⟨x, hxn⟩) := by
      rfl
    _ = localBrauerFactorialInvariant K n ⟨x, hxn⟩ :=
      localBrauerFactorialInvariant_inclusion K (Nat.le_max_right m n) ⟨x, hxn⟩

noncomputable def localBrauerFactorialISupInvariant
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ↥(⨆ n, localBrauerFactorialSlice K n) →+ RatModInt :=
  addSubgroupISupLift (localBrauerFactorialSlice K)
    (localBrauerFactorialSlices_directed K)
    (localBrauerFactorialInvariant K)
    (localBrauerFactorialInvariants_agree K)

noncomputable def localBrauerInvariantOfFactorialExhaustion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    BrauerGroup K →+ RatModInt :=
  addSubgroupISupLiftOfTop (localBrauerFactorialSlice K)
    (localBrauerFactorialSlices_directed K)
    (localBrauerFactorialInvariant K)
    (localBrauerFactorialInvariants_agree K) hTop

theorem localBrauerInvariantOfFactorialExhaustion_apply_stage
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤)
    (n : ℕ) (x : localBrauerFactorialSlice K n) :
    localBrauerInvariantOfFactorialExhaustion K hTop (x : BrauerGroup K) =
      localBrauerFactorialInvariant K n x := by
  exact addSubgroupISupLiftOfTop_apply_mem
    (localBrauerFactorialSlice K) (localBrauerFactorialSlices_directed K)
    (localBrauerFactorialInvariant K) (localBrauerFactorialInvariants_agree K)
    hTop n x

theorem localBrauerFactorialInvariant_injective
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Function.Injective (localBrauerFactorialInvariant K n) :=
  (zmodRatModIntAddHom_injective (localBrauerFactorialDegree n)
    (localBrauerFactorialDegree_ne_zero n)).comp
      (localBrauerFactorialCompatibleAddEquiv K n).symm.injective

theorem localBrauerInvariantOfFactorialExhaustion_injective
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    Function.Injective (localBrauerInvariantOfFactorialExhaustion K hTop) := by
  intro x y hxy
  have hmem : x - y ∈ ⨆ n, localBrauerFactorialSlice K n := by
    rw [hTop]
    exact AddSubgroup.mem_top _
  obtain ⟨n, hn⟩ :=
    (AddSubgroup.mem_iSup_of_directed (localBrauerFactorialSlices_directed K)).mp hmem
  let z : localBrauerFactorialSlice K n := ⟨x - y, hn⟩
  have hzglobal : localBrauerInvariantOfFactorialExhaustion K hTop (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzstage : localBrauerFactorialInvariant K n z = 0 := by
    rw [← localBrauerInvariantOfFactorialExhaustion_apply_stage K hTop n z]
    exact hzglobal
  have hz : z = 0 := localBrauerFactorialInvariant_injective K n
    (hzstage.trans (map_zero _).symm)
  apply sub_eq_zero.mp
  exact congrArg Subtype.val hz

theorem localBrauerInvariantOfFactorialExhaustion_surjective
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    Function.Surjective (localBrauerInvariantOfFactorialExhaustion K hTop) := by
  intro q
  obtain ⟨d, hd, hqd⟩ := ratModInt_exists_nonzero_nsmul_eq_zero q
  have hdiv : d ∣ localBrauerFactorialDegree d := by
    change d ∣ (d + 1).factorial
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hd) (Nat.le_add_right d 1)
  have hqD : q ∈ ratModIntNTorsion (localBrauerFactorialDegree d) :=
    ratModIntNTorsion_mono hdiv hqd
  have hqrange : q ∈ (zmodRatModIntAddHom (localBrauerFactorialDegree d)
      (localBrauerFactorialDegree_ne_zero d)).range := by
    rw [zmodRatModIntAddHom_range_eq_ratModIntNTorsion]
    exact hqD
  obtain ⟨z, hz⟩ := hqrange
  let x := localBrauerFactorialCompatibleAddEquiv K d z
  refine ⟨(x : BrauerGroup K), ?_⟩
  rw [localBrauerInvariantOfFactorialExhaustion_apply_stage K hTop d x]
  change zmodRatModIntAddHom (localBrauerFactorialDegree d)
    (localBrauerFactorialDegree_ne_zero d)
    ((localBrauerFactorialCompatibleAddEquiv K d).symm x) = q
  rw [(localBrauerFactorialCompatibleAddEquiv K d).symm_apply_apply]
  exact hz

noncomputable def localBrauerGroupAddEquivRatModIntOfFactorialExhaustion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (hTop : ⨆ n, localBrauerFactorialSlice K n = ⊤) :
    BrauerGroup K ≃+ RatModInt :=
  AddEquiv.ofBijective (localBrauerInvariantOfFactorialExhaustion K hTop)
    ⟨localBrauerInvariantOfFactorialExhaustion_injective K hTop,
      localBrauerInvariantOfFactorialExhaustion_surjective K hTop⟩

noncomputable def nonarchimedeanLocalBrauerGroupAddEquivRatModInt
    (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [IsUltrametricDist F] [LocallyCompactSpace F] :
    BrauerGroup F ≃+ RatModInt := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  exact localBrauerGroupAddEquivRatModIntOfFactorialExhaustion F
    (iSup_localBrauerFactorialSlice_eq_top F)

end

end GaloisForLFunctions.HTGeometry.ABHN
