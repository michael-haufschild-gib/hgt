import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Composition.Independence

/-! # Excitation thresholds of independently composed prime sectors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Composition

open Finset

variable {S T : Finset Nat.Primes} (c : S → ℕ) (m : ℕ) (d : T → ℕ) (n : ℕ)

/-- The product state has the product of its component integer labels. -/
def jointEnergy (z : State c m × State d n) := energy (level z.1 * level z.2)

def jointLower := Set.range fun z => jointEnergy c m d n z - (baseline price c m+baseline price d n)
def jointUpper := Set.range fun z => -(jointEnergy c m d n z) -
  (baseline reversePrice c m+baseline reversePrice d n)

theorem joint_edges :
    jointLower c m d n = sums (lowerEdge c m) (lowerEdge d n) ∧
    jointUpper c m d n = sums (upperEdge c m) (upperEdge d n) := by
  constructor <;> ext z <;> constructor
  · rintro ⟨⟨x,y⟩,rfl⟩
    exact ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,by simp only [jointEnergy,energy_mul]; ring⟩
  · rintro ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,rfl⟩
    exact ⟨(x,y),by simp only [jointEnergy,energy_mul]; ring⟩
  · rintro ⟨⟨x,y⟩,rfl⟩
    exact ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,by simp only [jointEnergy,energy_mul]; ring⟩
  · rintro ⟨_,⟨x,rfl⟩,_,⟨y,rfl⟩,rfl⟩
    exact ⟨(x,y),by simp only [jointEnergy,energy_mul]; ring⟩

/-- If either factor has no states, the product has no excitations. -/
def jointCandidates := if m ≤ capacity c ∧ n ≤ capacity d then candidates c m ∪ candidates d n else ∅

private theorem zero_edges (w : State c m) : (0 : ℝ) ∈ lowerEdge c m ∩ upperEdge c m := by
  obtain ⟨g,u,_,_,lo,hi,_⟩ := anchors w
  exact ⟨⟨g,by rw [lo]; exact sub_self _⟩,⟨u,by rw [hi]; exact sub_self _⟩⟩

private theorem positive_edges :
    (∀ z ∈ lowerEdge c m, 0 ≤ z) ∧ (∀ z ∈ upperEdge c m, 0 ≤ z) := by
  constructor <;> rintro _ ⟨x,rfl⟩
  · obtain ⟨g,_,_,_,lo,_,ext⟩ := anchors x
    exact sub_nonneg.mpr (lo ▸ (ext x).1)
  · obtain ⟨_,u,_,_,_,hi,ext⟩ := anchors x
    exact sub_nonneg.mpr (hi ▸ neg_le_neg (ext x).2)

private theorem lift_one {A B C D : Set ℝ} (zero : (0 : ℝ) ∈ C ∩ D)
    (unique : ∀ a ∈ A, ∀ b ∈ C, ∀ u ∈ B, ∀ v ∈ D, a+b=u+v → a=u) :
    differences A B ⊆ differences (sums A C) (sums B D) := by
  rintro z (⟨ha,hb⟩ | ⟨hb,ha⟩)
  · refine Or.inl ⟨⟨z,ha,0,zero.1,add_zero _⟩,?_⟩
    rintro ⟨u,hu,v,hv,he⟩
    exact hb ((unique z ha 0 zero.1 u hu v hv ((add_zero z).trans he.symm)).symm ▸ hu)
  · refine Or.inr ⟨⟨z,hb,0,zero.2,add_zero _⟩,?_⟩
    rintro ⟨u,hu,v,hv,he⟩
    exact ha (unique u hu v hv z hb 0 zero.2 (he.trans (add_zero z).symm) ▸ hu)

private theorem sums_comm (A B : Set ℝ) : sums A B = sums B A := by
  ext z
  constructor <;> rintro ⟨a,ha,b,hb,rfl⟩ <;> exact ⟨b,hb,a,ha,add_comm _ _⟩

private theorem component_below {A B C D : Set ℝ} (ha : ∀ z ∈ A, 0 ≤ z) (hc : ∀ z ∈ C, 0 ≤ z)
    {z : ℝ} (h : z ∈ sums A C \ sums B D) : ∃ t, (t ∈ A \ B ∨ t ∈ C \ D) ∧ t ≤ z := by
  obtain ⟨⟨a,h₁,b,h₂,rfl⟩,hu⟩ := h
  by_cases h₃ : a ∈ B
  · exact ⟨b,Or.inr ⟨h₂,fun h₄ => hu ⟨a,h₃,b,h₄,rfl⟩⟩,le_add_of_nonneg_left (ha _ h₁)⟩
  · exact ⟨a,Or.inl ⟨h₁,h₃⟩,le_add_of_nonneg_right (hc _ h₂)⟩

private theorem product_cover {z : ℝ}
    (hz : z ∈ differences (sums (lowerEdge c m) (lowerEdge d n)) (sums (upperEdge c m) (upperEdge d n))) :
    ∃ y ∈ candidates c m ∪ candidates d n, y ≤ z := by
  obtain ⟨hl,hu⟩ := positive_edges c m
  obtain ⟨hl',hu'⟩ := positive_edges d n
  have near : ∃ a, (a ∈ differences (lowerEdge c m) (upperEdge c m) ∨
      a ∈ differences (lowerEdge d n) (upperEdge d n)) ∧ a ≤ z := by
    rcases hz with low | high
    · obtain ⟨a,ha,hle⟩ := component_below hl hl' low
      exact ⟨a,ha.imp Or.inl Or.inl,hle⟩
    · obtain ⟨a,ha,hle⟩ := component_below hu hu' high
      exact ⟨a,ha.imp Or.inr Or.inr,hle⟩
  obtain ⟨a,ha,hle⟩ := near
  rcases ha with left | right
  · obtain ⟨y,hy,hy'⟩ := candidates_cover c m a left
    exact ⟨y,mem_union_left _ hy,hy'.trans hle⟩
  · obtain ⟨y,hy,hy'⟩ := candidates_cover d n a right
    exact ⟨y,mem_union_right _ hy,hy'.trans hle⟩

theorem joint_bounds (hd : Disjoint S T) :
    (↑(jointCandidates c m d n) ⊆ differences (jointLower c m d n) (jointUpper c m d n)) ∧
    ∀ z ∈ differences (jointLower c m d n) (jointUpper c m d n), ∃ y ∈ jointCandidates c m d n, y ≤ z := by
  classical
  by_cases feasible : m ≤ capacity c ∧ n ≤ capacity d
  · obtain ⟨w⟩ := (feasible_iff c m).mpr feasible.1
    obtain ⟨w'⟩ := (feasible_iff d n).mpr feasible.2
    rw [jointCandidates,if_pos feasible,(joint_edges c m d n).1,(joint_edges c m d n).2]
    refine ⟨?_,fun _ hz => product_cover c m d n hz⟩
    intro z hz
    rcases mem_union.mp hz with ha | hb
    · exact lift_one (zero_edges d n w') (fun _ a _ b _ u _ v he => (match_components hd a b u v he).1)
        (candidates_subset c m ha)
    · rw [sums_comm (lowerEdge c m),sums_comm (upperEdge c m)]
      exact lift_one (zero_edges c m w) (fun _ a _ b _ u _ v he => (match_components hd.symm a b u v he).1)
        (candidates_subset d n hb)
  · rw [jointCandidates,if_neg feasible,coe_empty]
    refine ⟨Set.empty_subset _,?_⟩
    intro z hz
    have absent (v : State c m × State d n) : False :=
      feasible ⟨(feasible_iff c m).mp ⟨v.1⟩,(feasible_iff d n).mp ⟨v.2⟩⟩
    rcases hz with ⟨⟨v,_⟩,_⟩ | ⟨⟨v,_⟩,_⟩ <;> exact (absent v).elim

/-- The first unpaired energy in the product is the minimum of the two factors' candidate lists. -/
theorem first_under_composition (hd : Disjoint S T) (h : (jointCandidates c m d n).Nonempty) :
    IsLeast (differences (jointLower c m d n) (jointUpper c m d n)) ((jointCandidates c m d n).min' h) := by
  obtain ⟨sub,cover⟩ := joint_bounds c m d n hd
  refine ⟨sub (min'_mem _ _),?_⟩
  intro z hz
  obtain ⟨y,hy,hle⟩ := cover z hz
  exact (min'_le _ _ hy).trans hle

theorem reflecting_product_iff (hd : Disjoint S T) :
    jointLower c m d n = jointUpper c m d n ↔
      ¬(m ≤ capacity c ∧ n ≤ capacity d) ∨ (lowerEdge c m = upperEdge c m ∧ lowerEdge d n = upperEdge d n) := by
  classical
  obtain ⟨sub,cover⟩ := joint_bounds c m d n hd
  have clear : jointLower c m d n = jointUpper c m d n ↔ jointCandidates c m d n = ∅ := by
    constructor
    · intro he
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hx := sub hy
      simp only [he,differences,Set.sdiff_self,Set.union_self,Set.mem_empty_iff_false] at hx
    · intro he
      ext z
      constructor <;> intro hz <;> by_contra hn
      · obtain ⟨_,hy,_⟩ := cover z (Or.inl ⟨hz,hn⟩)
        simp only [he,notMem_empty] at hy
      · obtain ⟨_,hy,_⟩ := cover z (Or.inr ⟨hz,hn⟩)
        simp only [he,notMem_empty] at hy
  rw [clear,jointCandidates]
  by_cases h : m ≤ capacity c ∧ n ≤ capacity d
  · rw [if_pos h,union_eq_empty,no_candidates_iff,no_candidates_iff,or_iff_right (not_not.mpr h)]
  · rw [if_neg h]
    exact ⟨fun _ => Or.inl h,fun _ => rfl⟩

#print axioms joint_edges
#print axioms joint_bounds
#print axioms first_under_composition
#print axioms reflecting_product_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold.Composition
