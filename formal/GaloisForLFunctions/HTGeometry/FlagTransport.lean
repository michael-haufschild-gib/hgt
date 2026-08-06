import GaloisForLFunctions.HTGeometry.AntitoneEigenframe
import GaloisForLFunctions.HTGeometry.HermitianFlat
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Transporting a degeneration flag by a symmetry

For every symmetry `g` of the observer space and every Hermitian direction `T` there is a Hermitian
direction `S` whose flag is the image of the flag of `T` under the adjoint of `g`, **with the same
thresholds**:

```text
eigenSum S c = (eigenSum T c).map g*.
```

The construction is Gram–Schmidt.  In an eigenframe of `T` ordered by decreasing eigenvalue every
flag member is the span of an initial segment, and Gram–Schmidt preserves the span of an initial
segment; so orthonormalising the images `g* b i` in that order and weighting the result by the same
eigenvalues produces the required direction.

This is the direction that the basepoint change assigns to the ray `t ↦ g* exp (t T) g`: the ray
through the reference metric that it is asymptotic to.
-/

namespace GaloisForLFunctions.HTGeometry

open Module InnerProductSpace

variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {T : E →ₗ[ℂ] E}

/-! ## Rescaling does not change spans -/

omit [FiniteDimensional ℂ E] in
theorem span_image_of_smul {ι : Type*} {f h : ι → E} {c : ι → ℂ} (hc : ∀ i, c i ≠ 0)
    (hh : ∀ i, h i = c i • f i) (s : Set ι) :
    Submodule.span ℂ (h '' s) = Submodule.span ℂ (f '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, hi, rfl⟩
    rw [hh i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · rintro _ ⟨i, hi, rfl⟩
    have : f i = (c i)⁻¹ • h i := by
      rw [hh i, smul_smul, inv_mul_cancel₀ (hc i), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

/-! ## Gram–Schmidt preserves initial spans -/

theorem span_gramSchmidtOrthonormalBasis_Iic (hcard : finrank ℂ E = Fintype.card (Fin n))
    {f : Fin n → E} (hf : LinearIndependent ℂ f) (k : Fin n) :
    Submodule.span ℂ (gramSchmidtOrthonormalBasis hcard f '' Set.Iic k)
      = Submodule.span ℂ (f '' Set.Iic k) := by
  have hne : ∀ i : Fin n, gramSchmidtNormed ℂ f i ≠ 0 := by
    intro i hcon
    have := gramSchmidtNormed_unit_length (𝕜 := ℂ) i hf
    rw [hcon, norm_zero] at this
    exact absurd this (by norm_num)
  have hgs : ∀ i : Fin n, gramSchmidtOrthonormalBasis hcard f i
      = ((‖gramSchmidt ℂ f i‖ : ℂ))⁻¹ • gramSchmidt ℂ f i := by
    intro i
    rw [gramSchmidtOrthonormalBasis_apply hcard (hne i), gramSchmidtNormed]
    rfl
  have hc : ∀ i : Fin n, ((‖gramSchmidt ℂ f i‖ : ℂ))⁻¹ ≠ 0 := by
    intro i
    refine inv_ne_zero ?_
    simpa using norm_ne_zero_iff.2 (gramSchmidt_ne_zero (𝕜 := ℂ) i hf)
  rw [span_image_of_smul hc hgs, span_gramSchmidt_Iic]

/-! ## The adjoint of a symmetry is injective -/

theorem adjoint_equiv_injective (g : E ≃ₗ[ℂ] E) :
    Function.Injective (LinearMap.adjoint (g : E →ₗ[ℂ] E)) := by
  have hcomp : LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) ∘ₗ
      LinearMap.adjoint ((g : E →ₗ[ℂ] E)) = LinearMap.id := by
    rw [← LinearMap.adjoint_comp,
      show ((g : E →ₗ[ℂ] E) ∘ₗ (g.symm : E →ₗ[ℂ] E)) = LinearMap.id from by
        ext v
        simp]
    exact LinearMap.adjoint_id
  refine Function.LeftInverse.injective
    (g := fun z => LinearMap.adjoint ((g.symm : E →ₗ[ℂ] E)) z) fun x => ?_
  exact congrArg (fun F : E →ₗ[ℂ] E => F x) hcomp

/-! ## Flag transport -/

/-- **Flag transport from a pair of frames.**  If the initial spans of a frame `gs` are the images
under `g*` of those of an antitone eigenframe of `T`, then the flag of the diagonal operator with
the same weights is the image of the flag of `T`. -/
theorem eigenSum_diagOp_eq_map (g : E ≃ₗ[ℂ] E) (b gs : OrthonormalBasis (Fin n) ℂ E)
    {w : Fin n → ℝ} (hw : Antitone w) (hd : ∀ i, T (b i) = ((w i : ℝ) : ℂ) • b i)
    (hspan : ∀ k : Fin n, Submodule.span ℂ (gs '' Set.Iic k)
      = Submodule.span ℂ ((fun i => LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) '' Set.Iic k))
    (c : ℝ) :
    eigenSum (diagOp gs w) c = (eigenSum T c).map (LinearMap.adjoint (g : E →ₗ[ℂ] E)) := by
  classical
  have hSspan : eigenSum (diagOp gs w) c
      = Submodule.span ℂ (gs '' {i : Fin n | c < w i}) := by
    have := eigenSum_eq_span_of_eigenbasis (T := diagOp gs w) gs.toBasis (w := w)
      (fun i => by rw [OrthonormalBasis.coe_toBasis]; exact diagOp_apply_basis gs w i) c
    rwa [OrthonormalBasis.coe_toBasis] at this
  have hTspan : eigenSum T c = Submodule.span ℂ (b '' {i : Fin n | c < w i}) := by
    have := eigenSum_eq_span_of_eigenbasis (T := T) b.toBasis (w := w)
      (fun i => by rw [OrthonormalBasis.coe_toBasis]; exact hd i) c
    rwa [OrthonormalBasis.coe_toBasis] at this
  have himg : ∀ s : Set (Fin n), (fun i => LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i)) '' s
      = (LinearMap.adjoint ((g : E →ₗ[ℂ] E))) '' (b '' s) := by
    intro s
    rw [← Set.image_comp]
    rfl
  rcases gt_set_eq_empty_or_Iic hw c with hempty | ⟨k, hk⟩
  · rw [hSspan, hTspan, hempty]
    simp
  · rw [hSspan, hTspan, hk, hspan k, himg (Set.Iic k), ← Submodule.span_image]

/-- **Flag transport.**  For every symmetry `g` and every Hermitian direction `T` there is a
Hermitian direction whose flag is the image of the flag of `T` by the adjoint of `g`, at the same
thresholds. -/
theorem exists_isSymmetric_eigenSum_map (g : E ≃ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hn : finrank ℂ E = n) :
    ∃ S : E →ₗ[ℂ] E, S.IsSymmetric ∧
      ∀ c : ℝ, eigenSum S c
        = (eigenSum T c).map (LinearMap.adjoint (g : E →ₗ[ℂ] E)) := by
  classical
  obtain ⟨b, w, hw, hd⟩ := exists_antitone_eigenframe hT hn
  set f : Fin n → E := fun i => LinearMap.adjoint ((g : E →ₗ[ℂ] E)) (b i) with hf
  have hcard : finrank ℂ E = Fintype.card (Fin n) := by
    rw [hn, Fintype.card_fin]
  have hLI : LinearIndependent ℂ f :=
    (b.toBasis.linearIndependent).map' (LinearMap.adjoint ((g : E →ₗ[ℂ] E)))
      (LinearMap.ker_eq_bot.2 (adjoint_equiv_injective g))
  exact ⟨diagOp (gramSchmidtOrthonormalBasis hcard f) w,
    isSymmetric_diagOp _ w,
    eigenSum_diagOp_eq_map g b _ hw hd (span_gramSchmidtOrthonormalBasis_Iic hcard hLI)⟩

end GaloisForLFunctions.HTGeometry
