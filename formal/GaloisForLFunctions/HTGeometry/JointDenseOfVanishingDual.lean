import GaloisForLFunctions.HTGeometry.DenseOfVanishingDual

/-!
# Joint density from a pair of vanishing functionals

A continuous functional on a product splits as a sum of one functional on each factor, so the
annihilator of a subspace of `E × F` is described by *pairs* `(f₁, f₂)` with `f₁ x + f₂ y = 0` on
the subspace.  Hence a joint-density statement — that a graph is dense in the whole product, not
merely that its two projections are dense — reduces to showing that no such pair except `(0, 0)`
annihilates it.

This is the shape of a joint-closure argument: density of the projections is strictly weaker, and
what rules out the intermediate closed subspaces is exactly the absence of a nonzero annihilating
pair.

* `HTGeometry.apply_eq_inl_add_inr`;
* `HTGeometry.topologicalClosure_eq_top_of_forall_pair_dual_eq_zero`;
* `HTGeometry.closure_add_left_image`, `HTGeometry.dense_affine_of_topologicalClosure_eq_top`.
-/

namespace HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous functional on a product is the sum of its restrictions to the two factors. -/
theorem apply_eq_inl_add_inr (f : (E × F) →L[ℝ] ℝ) (x : E) (y : F) :
    f (x, y) = f (x, 0) + f (0, y) := by
  have hsplit : ((x, y) : E × F) = (x, 0) + (0, y) := by
    ext <;> simp
  rw [hsplit, map_add]

/-- **Joint density from the absence of an annihilating pair.**  If the only pair of continuous
functionals `(f₁, f₂)` with `f₁ x + f₂ y = 0` throughout the subspace is the zero pair, then the
subspace is dense in the product. -/
theorem topologicalClosure_eq_top_of_forall_pair_dual_eq_zero
    (p : Submodule ℝ (E × F))
    (h : ∀ (f₁ : E →L[ℝ] ℝ) (f₂ : F →L[ℝ] ℝ),
      (∀ z ∈ p, f₁ z.1 + f₂ z.2 = 0) → (∀ x : E, f₁ x = 0) ∧ ∀ y : F, f₂ y = 0) :
    p.topologicalClosure = ⊤ := by
  refine topologicalClosure_eq_top_of_forall_dual_eq_zero p ?_
  intro f hf
  set f₁ : E →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ E F) with hf₁
  set f₂ : F →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inr ℝ E F) with hf₂
  have hval : ∀ (x : E) (y : F), f₁ x + f₂ y = f (x, y) := by
    intro x y
    rw [hf₁, hf₂]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    exact (apply_eq_inl_add_inr f x y).symm
  have hann : ∀ z ∈ p, f₁ z.1 + f₂ z.2 = 0 := by
    intro z hz
    rw [hval z.1 z.2]
    have hzz : ((z.1, z.2) : E × F) = z := rfl
    rw [hzz]
    exact hf z hz
  obtain ⟨h1, h2⟩ := h f₁ f₂ hann
  refine ContinuousLinearMap.ext fun z => ?_
  have hv := hval z.1 z.2
  have hz : ((z.1, z.2) : E × F) = z := rfl
  rw [hz] at hv
  rw [← hv, h1 z.1, h2 z.2, add_zero]
  rfl

omit [NormedSpace ℝ E] in
/-- Translation commutes with closure, being a homeomorphism. -/
theorem closure_add_left_image (v : E) (s : Set E) :
    closure ((fun x => v + x) '' s) = (fun x => v + x) '' closure s :=
  ((Homeomorph.addLeft v).image_closure s).symm

/-- **An affine translate of a dense subspace fills the space.**  This is the step from a joint
closure to its affine form: translating by a fixed vector is a homeomorphism, so the closure of the
translate is the translate of the closure. -/
theorem dense_affine_of_topologicalClosure_eq_top {p : Submodule ℝ E}
    (hp : p.topologicalClosure = ⊤) (v : E) :
    closure ((fun x => v + x) '' (p : Set E)) = Set.univ := by
  have hcl : closure (p : Set E) = Set.univ := by
    have hcoe : ((p.topologicalClosure : Submodule ℝ E) : Set E) = closure (p : Set E) :=
      Submodule.topologicalClosure_coe p
    rw [← hcoe, hp]
    rfl
  rw [closure_add_left_image, hcl]
  exact Set.image_univ_of_surjective (add_left_surjective v)

end HTGeometry
