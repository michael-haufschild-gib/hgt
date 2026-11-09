import Mathlib.Analysis.Convex.Intrinsic

/-!
# Exact convex correction in a symmetric phase hull

If the closure of a set is centrally symmetric, every strict radial contraction
of a point in that closure belongs to the convex hull of the original set.
Working in its linear span handles phase relations without a full-dimensionality
assumption in the ambient space.
-/

noncomputable section
set_option autoImplicit false

open Set Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem neg_mem_closure_convexHull {D : Set E}
    (hsym : ∀ x ∈ closure D, -x ∈ closure D) {x : E}
    (hx : x ∈ closure (convexHull ℝ D)) : -x ∈ closure (convexHull ℝ D) := by
  let C := closure (convexHull ℝ D)
  have hc : Convex ℝ C := (convex_convexHull ℝ D).closure
  have hpre : Convex ℝ ((fun y : E => -y) ⁻¹' C) := by
    intro u hu v hv a b ha hb hab
    simpa only [mem_preimage, neg_add, smul_neg] using hc hu hv ha hb hab
  have hD : D ⊆ (fun y : E => -y) ⁻¹' C := by
    intro y hy
    exact closure_mono (subset_convexHull ℝ D) (hsym y (subset_closure hy))
  exact closure_minimal (convexHull_min hD hpre)
    (isClosed_closure.preimage continuous_neg) hx

variable [FiniteDimensional ℝ E]

private theorem zero_mem_interior_convexHull {D : Set E}
    (hspan : affineSpan ℝ D = ⊤)
    (hsym : ∀ x ∈ closure D, -x ∈ closure D) :
    (0 : E) ∈ interior (convexHull ℝ D) := by
  have hc := convex_convexHull ℝ D
  have hspanC : affineSpan ℝ (convexHull ℝ D) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact affineSpan_mono ℝ (subset_convexHull ℝ D)
  have hne := hc.interior_nonempty_iff_affineSpan_eq_top.mpr hspanC
  obtain ⟨x, hx⟩ := hne
  have hx' : x ∈ interior (closure (convexHull ℝ D)) := interior_mono subset_closure hx
  have hneg : -x ∈ interior (closure (convexHull ℝ D)) := by
    have hsub : (fun y : E => -y) ⁻¹' interior (closure (convexHull ℝ D)) ⊆
        closure (convexHull ℝ D) := by
      intro y hy
      simpa only [neg_neg] using neg_mem_closure_convexHull hsym (interior_subset hy)
    apply interior_maximal hsub (isOpen_interior.preimage continuous_neg)
    simpa only [mem_preimage, neg_neg] using hx'
  have hzero := hc.closure.interior hx' hneg
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  rw [hc.interior_closure_eq_interior_of_nonempty_interior ⟨x, hx⟩] at hzero
  simpa only [smul_neg, add_neg_cancel] using hzero

/-- Strict contractions of closure points are exact finite convex combinations
of points of the original set whenever its closure is centrally symmetric. -/
theorem smul_mem_convexHull_of_symmetric_closure {D : Set E} (hne : D.Nonempty)
    (hsym : ∀ x ∈ closure D, -x ∈ closure D) {z : E} (hz : z ∈ closure D)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) : r • z ∈ convexHull ℝ D := by
  let V := Submodule.span ℝ D
  let D' : Set V := Subtype.val ⁻¹' D
  have himage : (fun x : V => (x : E)) '' D' = D := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx
    · intro x hx
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
  have hclosure : closure D' = Subtype.val ⁻¹' closure D := by
    exact (Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image D').trans
      (congrArg (fun S : Set E => (fun x : V => (x : E)) ⁻¹' closure S) himage)
  have hsym' : ∀ x ∈ closure D', -x ∈ closure D' := by
    intro x hx
    rw [hclosure] at hx ⊢
    exact hsym x hx
  have hne' : D'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, Submodule.subset_span hx⟩, hx⟩
  have hzero : (0 : V) ∈ affineSpan ℝ D' := by
    obtain ⟨x, hx⟩ := hne'
    have hxA := subset_affineSpan ℝ D' hx
    have hnA : -x ∈ affineSpan ℝ D' :=
      closure_minimal (subset_affineSpan ℝ D')
        (affineSpan ℝ D').closed_of_finiteDimensional (hsym' x (subset_closure hx))
    have hm := (affineSpan ℝ D').convex hxA hnA
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    convert hm using 1 <;> simp only [smul_neg, add_neg_cancel]
    rfl
  have hspan : Submodule.span ℝ D' = ⊤ := by
    apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
    rw [Submodule.map_span]
    change Submodule.span ℝ ((fun x : V => (x : E)) '' D') = _
    rw [himage]
    exact (Submodule.map_subtype_top V).symm
  have haff : affineSpan ℝ D' = ⊤ := by
    apply SetLike.coe_injective
    rw [← affineSpan_insert_eq_affineSpan ℝ hzero, affineSpan_insert_zero, hspan]
    rfl
  have hzV : z ∈ V :=
    closure_minimal (Submodule.subset_span) V.closed_of_finiteDimensional hz
  let z' : V := ⟨z, hzV⟩
  have hz' : z' ∈ closure D' := by
    rw [hclosure]
    exact hz
  have hconv : r • z' ∈ convexHull ℝ D' := by
    apply interior_subset
    have h := (convex_convexHull ℝ D').combo_interior_closure_mem_interior
      (zero_mem_interior_convexHull haff hsym')
      (closure_mono (subset_convexHull ℝ D') hz')
      (sub_pos.mpr hr1) hr0 (sub_add_cancel 1 r)
    simpa only [smul_zero, zero_add] using h
  have hmap : convexHull ℝ D' ⊆ V.subtype ⁻¹' convexHull ℝ D :=
    convexHull_min (fun _ hx => subset_convexHull ℝ D hx)
      ((convex_convexHull ℝ D).linear_preimage V.subtype)
  exact hmap hconv

#print axioms smul_mem_convexHull_of_symmetric_closure

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
