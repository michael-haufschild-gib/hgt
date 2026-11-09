import Mathlib.Analysis.Convex.Intrinsic

/-!
# Exact radial correction from a negative contraction

A nonempty convex set preserved by a fixed negative homothety contains zero in
its relative interior. In finite dimension every strict radial contraction of
a closure point therefore lies in the original convex set. Central symmetry
is unnecessary.
-/

noncomputable section
set_option autoImplicit false
open Set Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

private theorem negative_contraction_combo {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : ℝ) (x : E) :
    (a / (1 + a)) • x + (1 / (1 + a)) • ((-a) • x) = 0 := by
  rw [smul_smul, ← add_smul]
  have h : a / (1 + a) + 1 / (1 + a) * (-a) = 0 := by ring
  rw [h, zero_smul]

/-- A convex set preserved by a negative homothety contains the origin. -/
theorem zero_mem_of_negative_contraction {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : Set E} (hC : Convex ℝ C) (hne : C.Nonempty) {a : ℝ} (ha : 0 < a)
    (hneg : ∀ x ∈ C, (-a) • x ∈ C) : (0 : E) ∈ C := by
  obtain ⟨x, hx⟩ := hne
  have hd : 0 < 1 + a := by linarith only [ha]
  have hs : a / (1 + a) + 1 / (1 + a) = 1 := by
    rw [← add_div, add_comm a 1, div_self hd.ne']
  have h := hC hx (hneg x hx) (div_pos ha hd).le (one_div_pos.mpr hd).le hs
  rwa [negative_contraction_combo] at h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem zero_mem_interior_of_negative_contraction {C : Set E}
    (hC : Convex ℝ C) (hspan : affineSpan ℝ C = ⊤) {a : ℝ} (ha : 0 < a)
    (hneg : ∀ x ∈ C, (-a) • x ∈ C) : (0 : E) ∈ interior C := by
  obtain ⟨x, hx⟩ := hC.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
  have hd : 0 < 1 + a := by linarith only [ha]
  have hs : a / (1 + a) + 1 / (1 + a) = 1 := by
    rw [← add_div, add_comm a 1, div_self hd.ne']
  have h := hC.combo_interior_self_mem_interior hx (hneg x (interior_subset hx))
    (div_pos ha hd) (one_div_pos.mpr hd).le hs
  rwa [negative_contraction_combo] at h

/-- Strict radial contractions of closure points remain in a finite-dimensional
convex set preserved by a fixed negative homothety, even in a proper subspace. -/
theorem smul_mem_of_negative_contraction {C : Set E} (hC : Convex ℝ C)
    (hne : C.Nonempty) {a : ℝ} (ha : 0 < a) (hneg : ∀ x ∈ C, (-a) • x ∈ C)
    {z : E} (hz : z ∈ closure C) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : r • z ∈ C := by
  let V := Submodule.span ℝ C
  let C' : Set V := Subtype.val ⁻¹' C
  have himage : (fun x : V => (x : E)) '' C' = C := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
  have hclosure : closure C' = Subtype.val ⁻¹' closure C := by
    exact (Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image C').trans
      (congrArg (fun S : Set E => (fun x : V => (x : E)) ⁻¹' closure S) himage)
  have hc : Convex ℝ C' := by
    change Convex ℝ (V.subtype ⁻¹' C)
    exact hC.linear_preimage V.subtype
  have hn : ∀ x ∈ C', (-a) • x ∈ C' := by
    intro x hx
    exact hneg (x : E) hx
  have hne' : C'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Submodule.subset_span hx⟩, hx⟩
  have hz0 : (0 : V) ∈ C' := zero_mem_of_negative_contraction hc hne' ha hn
  have hspan : Submodule.span ℝ C' = ⊤ := by
    apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
    rw [Submodule.map_span]
    change Submodule.span ℝ ((fun x : V => (x : E)) '' C') = _
    rw [himage]
    exact (Submodule.map_subtype_top V).symm
  have haff : affineSpan ℝ C' = ⊤ := by
    apply SetLike.coe_injective
    rw [← affineSpan_insert_eq_affineSpan ℝ (subset_affineSpan ℝ C' hz0),
      affineSpan_insert_zero, hspan]
    rfl
  have hzV : z ∈ V :=
    closure_minimal Submodule.subset_span V.closed_of_finiteDimensional hz
  let z' : V := ⟨z, hzV⟩
  have hz' : z' ∈ closure C' := by
    rw [hclosure]
    exact hz
  have h := hc.combo_interior_closure_mem_interior
    (zero_mem_interior_of_negative_contraction hc haff ha hn) hz'
    (sub_pos.mpr hr1) hr0 (sub_add_cancel 1 r)
  simp only [smul_zero, zero_add] at h
  have hrz : r • z' ∈ C' := interior_subset h
  exact hrz

#print axioms smul_mem_of_negative_contraction

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
