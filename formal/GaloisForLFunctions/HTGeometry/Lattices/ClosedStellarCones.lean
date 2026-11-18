import GaloisForLFunctions.HTGeometry.LotzStellarCones

/-!
# Stellar subdivision of closed simplicial cones

A ray with nonnegative coordinates subdivides precisely its support face.
Minimum coordinate ratios describe every child and all ties on the boundary.
-/

namespace GaloisForLFunctions.HTGeometry
open Module Finset
open scoped NNReal Classical
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module ℝ E]

/-- Replacing a generator by a ray supported on an arbitrary nonempty face.
Coordinates outside that face may vanish. -/
def stellarFaceGenerator (b : Basis ι ℝ E) (a : ι → ℝ) (i j : ι) : E :=
  if j=i then b.equivFun.symm a else b j

/-- Closed cone with one generator replaced by the new ray. -/
def stellarFaceChild (b : Basis ι ℝ E) (a : ι → ℝ) (i : ι) :=
  PointedCone.hull ℝ (Set.range (stellarFaceGenerator b a i))

private theorem child_coordinates (b : Basis ι ℝ E) (a c : ι → ℝ) (i j : ι) :
    b.equivFun (∑ k, c k • stellarFaceGenerator b a i k) j =
      c i*a j + if j=i then 0 else c j := by
  have h (k : ι) : b.equivFun (stellarFaceGenerator b a i k) j =
      if k=i then a j else if k=j then 1 else 0 := by
    by_cases hk : k=i
    · rw [stellarFaceGenerator,if_pos hk,LinearEquiv.apply_symm_apply,if_pos hk]
    · simp [stellarFaceGenerator,hk,Basis.equivFun_self]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,h]
  by_cases hj : j = i
  · subst j
    have hs (k : ι) : c k*(if k=i then a i else if k=i then (1:ℝ) else 0) =
        if k=i then c i*a i else 0 := by by_cases hk : k=i <;> simp [hk]
    simp only [hs]
    simp
  · have hh (k : ι) : c k*(if k=i then a j else if k=j then 1 else 0) =
        (if k=i then c i*a j else 0)+(if k=j then c j else 0) := by
      by_cases hk : k=i <;> by_cases hk' : k=j <;> simp_all
    simp [hh,sum_add_distrib,hj]

private theorem child_mem_exists (b : Basis ι ℝ E) (a : ι → ℝ) (i : ι) (y : E) :
    y ∈ stellarFaceChild b a i ↔
      ∃ c : ι → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • stellarFaceGenerator b a i k = y := by
  change y ∈ Submodule.span ℝ≥0 (Set.range _) ↔ _
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c,hc⟩
    exact ⟨fun j => (c j).val,fun j => (c j).property,hc⟩
  · rintro ⟨c,hc,he⟩
    exact ⟨fun j => (⟨c j,hc j⟩ : ℝ≥0),he⟩

/-- The child containing a point is indexed by any coordinate minimizing
the ratio of that point to the new ray on its support. The inequalities
also specify all common boundaries. -/
theorem stellarFaceChild_iff (b : Basis ι ℝ E) (a : ι → ℝ) (i : ι) (hi : 0 < a i) (y : E) :
    y ∈ stellarFaceChild b a i ↔ 0 ≤ b.equivFun y i ∧
      ∀ j, (b.equivFun y i / a i)*a j ≤ b.equivFun y j := by
  rw [child_mem_exists]
  constructor
  · rintro ⟨c,hc,rfl⟩
    have hii : b.equivFun (∑ k, c k • stellarFaceGenerator b a i k) i = c i*a i := by
      rw [child_coordinates,if_pos rfl,add_zero]
    rw [hii,mul_div_cancel_right₀ _ hi.ne']
    refine ⟨mul_nonneg (hc i) hi.le,fun j => ?_⟩
    rw [child_coordinates]
    exact le_add_of_nonneg_right (by split_ifs <;> first | exact le_rfl | exact hc j)
  · rintro ⟨hyi,hmin⟩
    let r := b.equivFun y i/a i
    let c (j : ι) := if j=i then r else b.equivFun y j-r*a j
    refine ⟨c,fun j => ?_,b.equivFun.injective (funext fun j => ?_)⟩
    · dsimp only [c]
      split_ifs
      · exact div_nonneg hyi hi.le
      · exact sub_nonneg.mpr (hmin j)
    · rw [child_coordinates]
      by_cases hj : j=i
      · subst j
        simp [c,r,hi.ne']
      · simp [c,hj]

/-- The closed children cover the entire parent cone, including every
coordinate wall. The support may be a proper face of the parent. -/
theorem stellarFaceChild_cover (b : Basis ι ℝ E) (a : ι → ℝ) (hn : ∀ i, 0 ≤ a i)
    (hp : ∃ i, 0 < a i) :
    (lotzBasisCone b : Set E) = ⋃ i : {j // 0 < a j}, (stellarFaceChild b a i.val : Set E) := by
  ext y
  rw [Set.mem_iUnion]
  change (∀ j, 0 ≤ b.equivFun y j) ↔ ∃ i : {j // 0 < a j}, y ∈ stellarFaceChild b a i.val
  constructor
  · intro hy
    let S := univ.filter fun i => 0 < a i
    have hs : S.Nonempty := by obtain ⟨i,hi⟩ := hp; exact ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
    obtain ⟨i,hi,hm⟩ := exists_min_image S (fun j => b.equivFun y j/a j) hs
    have hai := (mem_filter.mp hi).2
    refine ⟨⟨i,hai⟩,(stellarFaceChild_iff b a i hai y).mpr ⟨hy i,fun j => ?_⟩⟩
    by_cases hj : 0 < a j
    · exact (le_div_iff₀ hj).mp (hm j (mem_filter.mpr ⟨mem_univ _,hj⟩))
    · simpa only [le_antisymm (le_of_not_gt hj) (hn j),mul_zero] using hy j
  · rintro ⟨i,hy⟩ j
    obtain ⟨hi,hj⟩ := (stellarFaceChild_iff b a _ i.property y).mp hy
    exact (mul_nonneg (div_nonneg hi i.property.le) (hn j)).trans (hj j)

/-- Inside a child, an additional child contains exactly the tied minimum
ratios. Strict minima therefore give the relatively disjoint sectors. -/
theorem stellarFaceChild_overlap (b : Basis ι ℝ E) (a : ι → ℝ) (i j : {k // 0 < a k})
    (y : E) (hy : y ∈ stellarFaceChild b a i.val) :
    y ∈ stellarFaceChild b a j.val ↔ b.equivFun y i.val/a i.val = b.equivFun y j.val/a j.val := by
  obtain ⟨hi,hmin⟩ := (stellarFaceChild_iff b a i.val i.property y).mp hy
  rw [stellarFaceChild_iff b a j.val j.property y]
  constructor
  · rintro ⟨_,hj⟩
    exact le_antisymm ((le_div_iff₀ j.property).mpr (hmin j.val))
      ((le_div_iff₀ i.property).mpr (hj i.val))
  · intro he
    refine ⟨(mul_nonneg (div_nonneg hi i.property.le) j.property.le).trans (hmin _),?_⟩
    rwa [← he]

#print axioms stellarFaceChild_iff
#print axioms stellarFaceChild_cover
#print axioms stellarFaceChild_overlap

end
end GaloisForLFunctions.HTGeometry
