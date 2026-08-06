import GaloisForLFunctions.HTGeometry.FlagTransport

/-!
# Triangularity of the transported frame

The Gram–Schmidt frame `gs` built from the images `g* b i` of an eigenframe `b` is *triangular*
against `b` in both directions:

```text
(g*)⁻¹ (gs j) ∈ span (b '' Set.Iic j),      g* (b i) ∈ span (gs '' Set.Iic i).
```

Together with an antitone weight vector these are what make the two pencils of a moved ray
uniformly bounded: in each expansion the exponent `t (w j - w i)` occurs only for `i ≤ j`, where
antitonicity makes it nonpositive.

The module also records the two elementary tools those estimates use: the operator norm of a map is
at most the sum of the norms of its values on an orthonormal frame, and a vector spanned by an
initial segment of a frame has vanishing coordinates beyond it.
-/

namespace GaloisForLFunctions.HTGeometry

open Module InnerProductSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## Bounding an operator by its values on a frame -/

theorem norm_toCLM_le_sum_norm_apply (b : OrthonormalBasis (Fin n) ℂ E) (M : E →ₗ[ℂ] E) :
    ‖LinearMap.toContinuousLinearMap M‖ ≤ ∑ i, ‖M (b i)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => norm_nonneg _) fun x => ?_
  have hx : M x = ∑ i, (b.repr x i) • M (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hcoeff : ∀ i, ‖b.repr x i‖ ≤ ‖x‖ := by
    intro i
    rw [b.repr_apply_apply]
    calc ‖(inner ℂ (b i) x : ℂ)‖ ≤ ‖b i‖ * ‖x‖ := norm_inner_le_norm _ _
      _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul]
  calc ‖M x‖ = ‖∑ i, (b.repr x i) • M (b i)‖ := by rw [hx]
    _ ≤ ∑ i, ‖(b.repr x i) • M (b i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖b.repr x i‖ * ‖M (b i)‖ := by
        exact Finset.sum_congr rfl fun i _ => norm_smul _ _
    _ ≤ ∑ i, ‖x‖ * ‖M (b i)‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul_of_nonneg_right (hcoeff i) (norm_nonneg _)
    _ = (∑ i, ‖M (b i)‖) * ‖x‖ := by
        rw [← Finset.mul_sum, mul_comm]

/-! ## Coordinates beyond an initial segment vanish -/

omit [FiniteDimensional ℂ E] in
theorem inner_eq_zero_of_mem_span_Iic (b : OrthonormalBasis (Fin n) ℂ E) {x : E} {j : Fin n}
    (hx : x ∈ Submodule.span ℂ (b '' Set.Iic j)) {i : Fin n} (hij : j < i) :
    (inner ℂ (b i) x : ℂ) = 0 := by
  have hsub : Submodule.span ℂ (b '' Set.Iic j) ≤ (ℂ ∙ b i)ᗮ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
    exact orthonormal_iff_ite.1 b.orthonormal k i |>.trans
      (if_neg fun hcon => absurd (hcon ▸ hk) (not_le.2 hij))
  have := hsub hx
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
  exact this

/-! ## The transported frame is triangular -/

variable {T : E →ₗ[ℂ] E}

theorem adjoint_symm_comp_adjoint (g : E ≃ₗ[ℂ] E) (x : E) :
    LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) (LinearMap.adjoint ((g : E →ₗ[ℂ] E)) x) = x := by
  have hcomp : LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) ∘ₗ
      LinearMap.adjoint ((g : E →ₗ[ℂ] E)) = LinearMap.id := by
    rw [← LinearMap.adjoint_comp,
      show ((g : E →ₗ[ℂ] E) ∘ₗ (g.symm : E →ₗ[ℂ] E)) = LinearMap.id from by
        ext v
        simp]
    exact LinearMap.adjoint_id
  exact congrArg (fun F : E →ₗ[ℂ] E => F x) hcomp

theorem adjoint_comp_adjoint_symm (g : E ≃ₗ[ℂ] E) (x : E) :
    LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) x) = x := by
  have hcomp : LinearMap.adjoint ((g : E →ₗ[ℂ] E)) ∘ₗ
      LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) = LinearMap.id := by
    rw [← LinearMap.adjoint_comp,
      show ((g.symm : E →ₗ[ℂ] E) ∘ₗ (g : E →ₗ[ℂ] E)) = LinearMap.id from by
        ext v
        simp]
    exact LinearMap.adjoint_id
  exact congrArg (fun F : E →ₗ[ℂ] E => F x) hcomp

/-- **The transported frame is spanned by the initial segments of the images.** -/
theorem gramSchmidt_mem_span_image (hcard : finrank ℂ E = Fintype.card (Fin n))
    {f : Fin n → E} (hf : LinearIndependent ℂ f) (j : Fin n) :
    gramSchmidtOrthonormalBasis hcard f j ∈ Submodule.span ℂ (f '' Set.Iic j) := by
  rw [← span_gramSchmidtOrthonormalBasis_Iic hcard hf j]
  exact Submodule.subset_span ⟨j, Set.mem_Iic.2 le_rfl, rfl⟩

/-- **The images are spanned by the initial segments of the transported frame.** -/
theorem mem_span_gramSchmidtOrthonormalBasis (hcard : finrank ℂ E = Fintype.card (Fin n))
    {f : Fin n → E} (hf : LinearIndependent ℂ f) (i : Fin n) :
    f i ∈ Submodule.span ℂ (gramSchmidtOrthonormalBasis hcard f '' Set.Iic i) := by
  rw [span_gramSchmidtOrthonormalBasis_Iic hcard hf i]
  exact Submodule.subset_span ⟨i, Set.mem_Iic.2 le_rfl, rfl⟩

/-- **Triangularity of the transported frame against the original one.**  The preimage under `g*`
of the `j`-th transported frame vector lies in the span of the first `j` original frame vectors. -/
theorem adjoint_symm_gramSchmidt_mem_span (g : E ≃ₗ[ℂ] E) (b : OrthonormalBasis (Fin n) ℂ E)
    (hcard : finrank ℂ E = Fintype.card (Fin n))
    (hf : LinearIndependent ℂ (fun i => LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i))) (j : Fin n) :
    LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E))
        (gramSchmidtOrthonormalBasis hcard (fun i => LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) j)
      ∈ Submodule.span ℂ (b '' Set.Iic j) := by
  have hmem := gramSchmidt_mem_span_image hcard hf j
  have himg : (fun i => LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) '' Set.Iic j
      = (LinearMap.adjoint ((g : E →ₗ[ℂ] E))) '' (b '' Set.Iic j) := by
    rw [← Set.image_comp]
    rfl
  rw [himg, Submodule.span_image] at hmem
  obtain ⟨y, hy, hyeq⟩ := hmem
  rw [← hyeq, adjoint_symm_comp_adjoint]
  exact hy

end GaloisForLFunctions.HTGeometry
