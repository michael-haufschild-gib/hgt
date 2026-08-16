import Mathlib

/-!
# A convex open set minus a countable set stays path connected

Mathlib removes a countable set from a whole plane; the identity theorem needs the same statement
inside a domain.  The two-segment argument survives verbatim: the broken line through `c + t·y` lies
in the convex set for every small `t`, and only countably many `t` meet the removed set, so a good
`t` exists in every neighbourhood of `0`.
-/

open Set Metric
open scoped Convex

namespace GaloisForLFunctions.HTGeometry

/-- **A convex open set minus a countable set is path connected.** -/
theorem isPathConnected_diff_of_countable_of_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hrank : 1 < Module.rank ℝ E) {V : Set E} (hV : Convex ℝ V)
    (hVo : IsOpen V) {Z : Set E} (hZ : Z.Countable) {a : E} (ha : a ∈ V \ Z) :
    IsPathConnected (V \ Z) := by
  refine ⟨a, ha, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ha
  set c : E := (2 : ℝ)⁻¹ • (a + b) with hcdef
  set x : E := (2 : ℝ)⁻¹ • (b - a) with hxdef
  have Ia : c - x = a := by rw [hcdef, hxdef]; module
  have Ib : c + x = b := by rw [hcdef, hxdef]; module
  have hcV : c ∈ V := by
    have h := hV ha.1 hb.1 (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (0:ℝ) ≤ 2⁻¹)
      (by norm_num : (2:ℝ)⁻¹ + 2⁻¹ = 1)
    have hEq : (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b = c := by rw [hcdef]; module
    rwa [hEq] at h
  have x_ne_zero : x ≠ 0 := by
    rw [hxdef]
    simp only [ne_eq, smul_eq_zero, sub_eq_zero]
    intro h
    rcases h with h | h
    · norm_num at h
    · exact hab h.symm
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank hrank x_ne_zero
  have hA : Set.Countable {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ Z).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hZ
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c + x} ∩ Z = ∅ := by
      simpa only [singleton_inter_eq_empty, Ib] using hb.2
    rw [inter_assoc, inter_comm Z, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have hB : Set.Countable {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ Z).Nonempty} := by
    apply countable_setOf_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hZ
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have N : {c - x} ∩ Z = ∅ := by
      simpa only [singleton_inter_eq_empty, Ia] using ha.2
    rw [inter_assoc, inter_comm Z, inter_assoc, inter_self, ← inter_assoc, ← subset_empty_iff, ← N]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert! hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  -- the segment stays in `V` for every small `t`
  set O : Set ℝ := {t : ℝ | c + t • y ∈ V} with hOdef
  have hOopen : IsOpen O := by
    have hcont : Continuous fun t : ℝ => c + t • y := by fun_prop
    exact hVo.preimage hcont
  have hOne : O.Nonempty := ⟨0, by simpa [hOdef] using hcV⟩
  obtain ⟨t, ht⟩ : (O ∩ ({t : ℝ | ([c + x -[ℝ] c + t • y] ∩ Z).Nonempty}
      ∪ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ Z).Nonempty})ᶜ).Nonempty :=
    Dense.inter_open_nonempty ((hA.union hB).dense_compl ℝ) O hOopen hOne
  have htO : c + t • y ∈ V := ht.1
  have ht' := ht.2
  simp only [compl_union, mem_inter_iff, mem_compl_iff, mem_setOf_eq] at ht'
  have JA : JoinedIn (V \ Z) a (c + t • y) := by
    refine JoinedIn.of_segment_subset ?_
    intro w hw
    rw [Ia] at ht'
    refine ⟨hV.segment_subset ha.1 htO hw, ?_⟩
    intro hwZ
    exact ht'.2 ⟨w, hw, hwZ⟩
  have JB : JoinedIn (V \ Z) b (c + t • y) := by
    refine JoinedIn.of_segment_subset ?_
    intro w hw
    rw [Ib] at ht'
    refine ⟨hV.segment_subset hb.1 htO hw, ?_⟩
    intro hwZ
    exact ht'.1 ⟨w, hw, hwZ⟩
  exact JA.trans JB.symm

/-- The complex instance: a convex open subset of the plane minus a countable set is
preconnected. -/
theorem isPreconnected_diff_of_countable_of_convex_complex {V : Set ℂ} (hV : Convex ℝ V)
    (hVo : IsOpen V) {Z : Set ℂ} (hZ : Z.Countable) {a : ℂ} (ha : a ∈ V \ Z) :
    IsPreconnected (V \ Z) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  exact (isPathConnected_diff_of_countable_of_convex hrank hV hVo hZ ha).isConnected.isPreconnected

end GaloisForLFunctions.HTGeometry
