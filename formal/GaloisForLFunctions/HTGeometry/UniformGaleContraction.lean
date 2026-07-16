import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Circuit

/-!
# Uniform Gale contraction

This module formalizes the finite combinatorial skeleton behind the proposed multiple-Gamma
Gale--Kolchin comparison.  The dual of a uniform rank-`k` matroid on a finite ground set has rank
`|E|-k`, and contracting one element of the dual of a uniform rank-two matroid leaves the
cardinality complex with faces of size at most `r-1` on `r+1` labels.

No special-function or differential-algebraic assertion is assumed here.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped Matroid

noncomputable section

variable {α : Type*} [Finite α]

/-- The uniform matroid of rank at most `k` on the finite ground set `E`. -/
def uniformMatroidOn (E : Set α) (k : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite E.toFinite
    (fun I : Set α => I ⊆ E ∧ I.ncard ≤ k)
    (by simp)
    (by
      intro I J hJ hIJ
      exact ⟨hIJ.trans hJ.1,
        (Set.ncard_le_ncard hIJ (E.toFinite.subset hJ.1)).trans hJ.2⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard
      refine ⟨e, heJ, heI, insert_subset (hJ.1 heJ) hI.1, ?_⟩
      rw [Set.ncard_insert_of_notMem heI]
      omega)
    (fun _ hI => hI.1)).matroid

@[simp] theorem uniformMatroidOn_ground (E : Set α) (k : ℕ) :
    (uniformMatroidOn E k).E = E := rfl

@[simp] theorem uniformMatroidOn_indep_iff (E I : Set α) (k : ℕ) :
    (uniformMatroidOn E k).Indep I ↔ I ⊆ E ∧ I.ncard ≤ k := by
  rfl

/-- In the nontruncated rank range, the bases of a uniform matroid are exactly the `k`-subsets of
its ground set. -/
theorem uniformMatroidOn_isBase_iff {E B : Set α} {k : ℕ} (hk : k ≤ E.ncard) :
    (uniformMatroidOn E k).IsBase B ↔ B ⊆ E ∧ B.ncard = k := by
  constructor
  · intro hB
    have hI := (uniformMatroidOn_indep_iff E B k).mp hB.indep
    refine ⟨hI.1, le_antisymm hI.2 ?_⟩
    by_contra hnot
    have hlt : B.ncard < k := by omega
    have hBE : B.ncard < E.ncard := hlt.trans_le hk
    obtain ⟨e, heE, heB⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hBE
    have hins : (uniformMatroidOn E k).Indep (insert e B) := by
      rw [uniformMatroidOn_indep_iff]
      refine ⟨insert_subset heE hI.1, ?_⟩
      rw [Set.ncard_insert_of_notMem heB]
      omega
    exact heB (hB.mem_of_insert_indep hins)
  · rintro ⟨hBE, hcard⟩
    have hI : (uniformMatroidOn E k).Indep B := by
      rw [uniformMatroidOn_indep_iff]
      exact ⟨hBE, hcard.le⟩
    apply hI.isBase_of_forall_insert
    intro e he
    rw [uniformMatroidOn_indep_iff]
    rintro ⟨-, hle⟩
    rw [Set.ncard_insert_of_notMem he.2, hcard] at hle
    omega

/-- Duality exchanges rank `k` with corank `|E|-k` for finite uniform matroids. -/
theorem uniformMatroidOn_dual {E : Set α} {k : ℕ} (hk : k ≤ E.ncard) :
    (uniformMatroidOn E k)✶ = uniformMatroidOn E (E.ncard - k) := by
  refine Matroid.ext_isBase
    (M₁ := (uniformMatroidOn E k)✶)
    (M₂ := uniformMatroidOn E (E.ncard - k)) rfl ?_
  intro B hBE
  rw [Matroid.dual_isBase_iff (M := uniformMatroidOn E k) hBE,
    uniformMatroidOn_isBase_iff hk,
    uniformMatroidOn_isBase_iff (Nat.sub_le E.ncard k)]
  have hBE' : B ⊆ E := by simpa using hBE
  have hBncard : B.ncard ≤ E.ncard := Set.ncard_le_ncard hBE' E.toFinite
  simp only [uniformMatroidOn_ground]
  rw [Set.ncard_diff hBE']
  constructor <;> rintro ⟨-, hcard⟩
  · exact ⟨hBE, by omega⟩
  · exact ⟨diff_subset, by omega⟩

/-- Contracting a nonloop from a positive-rank uniform matroid lowers both the ground-cardinality
and the rank by one. -/
theorem uniformMatroidOn_contractElem {E : Set α} {k : ℕ} {e : α}
    (he : e ∈ E) (hkpos : 0 < k) :
    uniformMatroidOn E k ／ {e} = uniformMatroidOn (E \ {e}) (k - 1) := by
  have heI : (uniformMatroidOn E k).Indep ({e} : Set α) := by
    rw [uniformMatroidOn_indep_iff]
    constructor
    · simpa using he
    · simpa using hkpos
  refine Matroid.ext_indep
    (M₁ := uniformMatroidOn E k ／ {e})
    (M₂ := uniformMatroidOn (E \ {e}) (k - 1)) rfl ?_
  intro I hIE
  rw [heI.contract_indep_iff, uniformMatroidOn_indep_iff,
    uniformMatroidOn_indep_iff]
  have he_not_mem : e ∉ I := by
    intro hei
    exact (hIE hei).2 (by simp)
  have hI_E : I ⊆ E := hIE.trans diff_subset
  have hIE' : I ⊆ E \ {e} := by simpa using hIE
  have hinsert_E : insert e I ⊆ E := insert_subset he hI_E
  rw [union_singleton, Set.ncard_insert_of_notMem he_not_mem]
  simp only [hIE', hinsert_E, true_and]
  constructor
  · rintro ⟨-, hle⟩
    apply (Nat.le_sub_one_iff_lt hkpos).2
    omega
  · intro hle
    have hlt : I.ncard < k := (Nat.le_sub_one_iff_lt hkpos).1 hle
    exact ⟨by simp [Set.disjoint_singleton_right, he_not_mem], by omega⟩

/-- **Uniform Gale contraction.**  The dual of a uniform rank-two configuration on `r+2`
labels, contracted by one distinguished label, is the uniform rank-`r-1` matroid on the remaining
`r+1` labels. -/
theorem uniformRankTwo_dual_contract_distinguished (r : ℕ) (hr : 1 ≤ r) :
    (uniformMatroidOn (Set.univ : Set (Fin (r + 2))) 2)✶ ／
        ({(0 : Fin (r + 2))} : Set (Fin (r + 2))) =
      uniformMatroidOn
        ((Set.univ : Set (Fin (r + 2))) \ {(0 : Fin (r + 2))}) (r - 1) := by
  rw [uniformMatroidOn_dual (E := (Set.univ : Set (Fin (r + 2))))
    (k := 2) (by simp)]
  have hcard : (Set.univ : Set (Fin (r + 2))).ncard - 2 = r := by simp
  rw [hcard]
  exact uniformMatroidOn_contractElem (E := (Set.univ : Set (Fin (r + 2))))
    (k := r) (e := (0 : Fin (r + 2))) (by simp) (by omega)

/-- The faces of the contracted Gale complex are exactly the subsets of the remaining labels of
cardinality at most `r-1`. -/
theorem uniformRankTwo_dual_contract_indep_iff (r : ℕ) (hr : 1 ≤ r)
    (I : Set (Fin (r + 2))) :
    ((uniformMatroidOn (Set.univ : Set (Fin (r + 2))) 2)✶ ／
        ({(0 : Fin (r + 2))} : Set (Fin (r + 2)))).Indep I ↔
      I ⊆ (Set.univ \ {(0 : Fin (r + 2))}) ∧ I.ncard ≤ r - 1 := by
  rw [uniformRankTwo_dual_contract_distinguished r hr,
    uniformMatroidOn_indep_iff]

/-- The dependent sets of the contracted Gale complex are precisely the remaining-label packets
of cardinality at least `r`. -/
theorem uniformRankTwo_dual_contract_dep_iff (r : ℕ) (hr : 1 ≤ r)
    (I : Set (Fin (r + 2))) :
    ((uniformMatroidOn (Set.univ : Set (Fin (r + 2))) 2)✶ ／
        ({(0 : Fin (r + 2))} : Set (Fin (r + 2)))).Dep I ↔
      I ⊆ (Set.univ \ {(0 : Fin (r + 2))}) ∧ r ≤ I.ncard := by
  rw [Matroid.dep_iff, uniformRankTwo_dual_contract_indep_iff r hr]
  constructor
  · rintro ⟨hnot, hsub⟩
    refine ⟨hsub, ?_⟩
    by_contra hlt
    apply hnot
    exact ⟨hsub, by omega⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨?_, hsub⟩
    rintro ⟨-, hle⟩
    omega

end

end GaloisForLFunctions.HTGeometry
