import Mathlib.GroupTheory.Finiteness
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Generating a group from a fundamental open set

If a group acts on a **connected** space by homeomorphisms and a single open set `V` already covers
the space under the action, then the elements that move `V` so that it still meets itself already
generate the group: the translates by the subgroup they generate form an open set, the remaining
translates form its open complement, and connectedness forbids a nontrivial splitting.

Combined with proper discontinuity — only finitely many group elements move a compact set to a set
meeting it — this is the standard source of finite generation for groups acting on contractible
spaces, and hence for arithmetic groups acting on their reduction-theoretic retracts.

* `closure_meet_set_eq_top` : **the generation lemma.**
* `fg_of_finite_meet_set` : finitely many such elements makes the group finitely generated.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Pointwise

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- The elements whose translate of `V` still meets `V`. -/
def meetSet (V : Set X) : Set G := {g : G | (g • V ∩ V).Nonempty}

omit [TopologicalSpace X] [ContinuousConstSMul G X] in
theorem one_mem_meetSet {V : Set X} (hV : V.Nonempty) : (1 : G) ∈ meetSet V := by
  obtain ⟨x, hx⟩ := hV
  exact ⟨x, by simpa using hx, hx⟩

/-- **The generation lemma.**  On a connected space an open set whose translates cover generates:
the elements moving `V` to a set meeting `V` generate the whole group. -/
theorem closure_meetSet_eq_top [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X)) :
    Subgroup.closure (meetSet (G := G) V) = ⊤ := by
  set H := Subgroup.closure (meetSet (G := G) V) with hH
  set A : Set X := ⋃ h : H, (h : G) • V with hA
  set B : Set X := ⋃ g : {g : G // g ∉ H}, (g : G) • V with hB
  have hAopen : IsOpen A := isOpen_iUnion fun _ => hVopen.smul _
  have hBopen : IsOpen B := isOpen_iUnion fun _ => hVopen.smul _
  have hunion : A ∪ B = univ := by
    rw [← hcover]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨h, hxh⟩ := mem_iUnion.1 hx
        exact mem_iUnion.2 ⟨(h : G), hxh⟩
      · obtain ⟨g, hxg⟩ := mem_iUnion.1 hx
        exact mem_iUnion.2 ⟨(g : G), hxg⟩
    · intro x hx
      obtain ⟨g, hxg⟩ := mem_iUnion.1 hx
      by_cases hg : g ∈ H
      · exact Or.inl (mem_iUnion.2 ⟨⟨g, hg⟩, hxg⟩)
      · exact Or.inr (mem_iUnion.2 ⟨⟨g, hg⟩, hxg⟩)
  have hdisj : A ∩ B = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    rintro x ⟨hxA, hxB⟩
    obtain ⟨h, hxh⟩ := mem_iUnion.1 hxA
    obtain ⟨g, hxg⟩ := mem_iUnion.1 hxB
    have hmeet : (((h : G)⁻¹ * (g : G)) • V ∩ V).Nonempty := by
      refine ⟨(h : G)⁻¹ • x, ?_, ?_⟩
      · rw [mul_smul]
        exact smul_mem_smul_set (by simpa using hxg)
      · have : (h : G)⁻¹ • x ∈ (h : G)⁻¹ • ((h : G) • V) := smul_mem_smul_set hxh
        simpa [smul_smul] using this
    have : (h : G)⁻¹ * (g : G) ∈ H := Subgroup.subset_closure hmeet
    exact g.2 (by simpa using mul_mem h.2 this)
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hVne
    exact ⟨x, mem_iUnion.2 ⟨⟨1, one_mem H⟩, by simpa using hx⟩⟩
  have hAeqBcompl : A = Bᶜ := by
    refine Set.eq_of_subset_of_subset (fun x hxA hxB => ?_) (fun x hxB => ?_)
    · exact absurd (mem_inter hxA hxB) (by rw [hdisj]; exact notMem_empty x)
    · rcases (hunion ▸ mem_univ x : x ∈ A ∪ B) with h | h
      · exact h
      · exact absurd h hxB
  have hclopen : IsClopen A := ⟨by rw [hAeqBcompl]; exact hBopen.isClosed_compl, hAopen⟩
  have hAuniv : A = univ := (isClopen_iff.1 hclopen).resolve_left hAne.ne_empty
  have hBempty : B = ∅ := by
    have hcompl : Aᶜ = B := by rw [hAeqBcompl, compl_compl]
    rw [← hcompl, hAuniv, compl_univ]
  refine Subgroup.eq_top_iff' _ |>.2 fun g => ?_
  by_contra hg
  obtain ⟨x, hx⟩ := hVne
  have : g • x ∈ B := mem_iUnion.2 ⟨⟨g, hg⟩, smul_mem_smul_set hx⟩
  rw [hBempty] at this
  exact this

/-- Finitely many elements moving `V` to a set that meets `V` makes the group finitely generated. -/
theorem fg_of_finite_meetSet [ConnectedSpace X] {V : Set X} (hVopen : IsOpen V)
    (hVne : V.Nonempty) (hcover : ⋃ g : G, g • V = (univ : Set X))
    (hfin : (meetSet (G := G) V).Finite) : Group.FG G :=
  Group.fg_iff.2 ⟨meetSet V, closure_meetSet_eq_top hVopen hVne hcover, hfin⟩

/-- **A group acting properly discontinuously on a connected space, with a relatively compact open
set whose translates cover the space, is finitely generated.** -/
theorem fg_of_properlyDiscontinuousSMul [ConnectedSpace X] [ProperlyDiscontinuousSMul G X]
    {V K : Set X} (hVopen : IsOpen V) (hVne : V.Nonempty) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcover : ⋃ g : G, g • V = (univ : Set X)) : Group.FG G := by
  refine fg_of_finite_meetSet hVopen hVne hcover ?_
  refine Set.Finite.subset
    (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := G) hK hK) ?_
  rintro g ⟨x, hx1, hx2⟩
  refine ⟨x, ?_, hVK hx2⟩
  rw [Set.image_smul]
  exact Set.smul_set_mono hVK hx1

end GaloisForLFunctions.HTGeometry
