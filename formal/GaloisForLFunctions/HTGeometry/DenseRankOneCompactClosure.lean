import GaloisForLFunctions.HTGeometry.CompactOperatorIdealSimplicity

/-! Dense vector families generate exactly the compact operators through their rank-one pairs. -/

noncomputable section
open Filter Topology InnerProductSpace
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def rankOneFamilySpan (v : ι → H) : Submodule ℂ (H →L[ℂ] H) :=
  Submodule.span ℂ (Set.range fun ij : ι × ι => rankOne ℂ (v ij.1) (v ij.2))

theorem rankOne_mem_closedFamilySpan (v : ι → H)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H)) (x y : H) :
    rankOne ℂ x y ∈ (rankOneFamilySpan v).topologicalClosure := by
  let K := (rankOneFamilySpan v).topologicalClosure
  have hbase (i j : ι) : rankOne ℂ (v i) (v j) ∈ K :=
    (rankOneFamilySpan v).le_topologicalClosure (Submodule.subset_span ⟨(i,j),rfl⟩)
  have hcol (j : ι) (a : H) : rankOne ℂ a (v j) ∈ K := by
    apply hd.induction (P := fun a => rankOne ℂ a (v j) ∈ K) _ _ a
    · intro b hb
      refine Submodule.span_induction (fun u hu => ?_) (by simp [K])
        (fun u w _ _ hu hw => ?_) (fun c u _ hu => ?_) hb
      · obtain ⟨i,rfl⟩ := hu
        exact hbase i j
      · simpa only [map_add, add_apply] using K.add_mem hu hw
      · simpa only [map_smul, smul_apply] using K.smul_mem c hu
    · exact (rankOneFamilySpan v).isClosed_topologicalClosure.preimage
        (((rankOne ℂ : H →L[ℂ] H →L⋆[ℂ] H →L[ℂ] H).flip (v j)).continuous)
  apply hd.induction (P := fun b => rankOne ℂ x b ∈ K) _ _ y
  · intro b hb
    refine Submodule.span_induction (fun u hu => ?_) (by simp [K])
      (fun u w _ _ hu hw => ?_) (fun c u _ hu => ?_) hb
    · obtain ⟨j,rfl⟩ := hu
      exact hcol j x
    · simpa only [map_add] using K.add_mem hu hw
    · simpa only [map_smulₛₗ] using K.smul_mem ((starRingEnd ℂ) c) hu
  · exact (rankOneFamilySpan v).isClosed_topologicalClosure.preimage
      ((rankOne ℂ x).continuous)

/-- The norm-closed span of rank-one pairs of a total family is exactly all compact operators. -/
theorem closed_rankOneFamilySpan_eq_compactOperator (v : ι → H)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set H)) :
    (rankOneFamilySpan v).topologicalClosure = compactOperator (RingHom.id ℂ) H H := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨i,j⟩,rfl⟩
      exact isCompactOperator_innerRankOne (v i) (v j)
    · exact isClosed_setOf_isCompactOperator
  · intro T hT
    obtain ⟨F,hF,hFT⟩ := exists_finiteRank_tendsto hT
    apply (rankOneFamilySpan v).isClosed_topologicalClosure.mem_of_tendsto hFT
    apply Eventually.of_forall
    intro n
    obtain ⟨k,hk⟩ := hF n
    obtain ⟨κ,_,b,c,he⟩ := exists_eq_sum_rankOne hk
    rw [he]
    exact Submodule.sum_mem _ fun i _ => rankOne_mem_closedFamilySpan v hd (b i) (c i)

end GaloisForLFunctions.HTGeometry
