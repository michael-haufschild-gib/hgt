import GaloisForLFunctions.HTGeometry.FiniteBlaschkeLeakageRank

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Projection of a bounded Hardy numerator onto an arbitrary closed model channel. -/
def modelSpaceLeakageCore (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (A : H →L[ℂ] H) : H →L[ℂ] K :=
  (K.starProjection.codRestrict K (fun x => K.starProjection_apply_mem x)).comp A

theorem adjoint_modelSpaceLeakageCore_apply
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [CompleteSpace K]
    (A : H →L[ℂ] H) (y : K) :
    (modelSpaceLeakageCore K A).adjoint y = A.adjoint (y : H) := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (y : H) (K.starProjection (A x)) =
    inner ℂ (y : H) (A x)
  have hperp : inner ℂ (y : H) (A x - K.starProjection (A x)) = 0 :=
    (K.mem_orthogonal _).1 (K.sub_starProjection_mem_orthogonal (A x)) y y.property
  calc
    inner ℂ (y : H) (K.starProjection (A x)) =
        inner ℂ (y : H) (K.starProjection (A x)) + 0 := by rw [add_zero]
    _ = inner ℂ (y : H) (K.starProjection (A x)) +
        inner ℂ (y : H) (A x - K.starProjection (A x)) := by rw [hperp]
    _ = inner ℂ (y : H)
        (K.starProjection (A x) + (A x - K.starProjection (A x))) := by
      rw [inner_add_right]
    _ = inner ℂ (y : H) (A x) := by congr 1; abel

/-- Faithfulness of the numerator adjoint on a model channel makes leakage dense in that channel. -/
theorem denseRange_modelSpaceLeakageCore
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [CompleteSpace K]
    (A : H →L[ℂ] H)
    (hinj : Function.Injective (A.adjoint.toLinearMap.domRestrict K)) :
    DenseRange (modelSpaceLeakageCore K A) := by
  have hadj : Function.Injective (modelSpaceLeakageCore K A).adjoint := by
    intro x y hxy
    apply hinj
    change A.adjoint (x : H) = A.adjoint (y : H)
    simpa only [adjoint_modelSpaceLeakageCore_apply] using hxy
  have hdense : DenseRange (modelSpaceLeakageCore K A).adjoint.adjoint := by
    change Dense ((((modelSpaceLeakageCore K A).adjoint.adjoint.range :
      Submodule ℂ K)) : Set K)
    rw [Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    rw [(modelSpaceLeakageCore K A).adjoint.adjoint.orthogonal_range,
      ContinuousLinearMap.adjoint_adjoint]
    exact LinearMap.ker_eq_bot.mpr hadj
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hdense

/-- In a finite-dimensional model channel, faithfulness of the numerator adjoint upgrades dense
projected leakage to surjectivity. -/
theorem modelSpaceLeakageCore_surjective_of_finiteDimensional
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [CompleteSpace K]
    [FiniteDimensional ℂ K] (A : H →L[ℂ] H)
    (hinj : Function.Injective (A.adjoint.toLinearMap.domRestrict K)) :
    Function.Surjective (modelSpaceLeakageCore K A) := by
  have hadj : Function.Injective (modelSpaceLeakageCore K A).adjoint := by
    intro x y hxy
    apply hinj
    change A.adjoint (x : H) = A.adjoint (y : H)
    simpa only [adjoint_modelSpaceLeakageCore_apply] using hxy
  have hsurj : Function.Surjective
      (modelSpaceLeakageCore K A).adjoint.adjoint :=
    adjoint_surjective_of_finiteDimensional_domain_injective
      (modelSpaceLeakageCore K A).adjoint hadj
  simpa only [ContinuousLinearMap.adjoint_adjoint] using hsurj

/-- Exact algebraic range dimension of faithful projected leakage into a finite model channel. -/
theorem finrank_range_modelSpaceLeakageCore_of_finiteDimensional
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [CompleteSpace K]
    [FiniteDimensional ℂ K] (A : H →L[ℂ] H)
    (hinj : Function.Injective (A.adjoint.toLinearMap.domRestrict K)) :
    Module.finrank ℂ (modelSpaceLeakageCore K A).range = Module.finrank ℂ K := by
  have hrange : (modelSpaceLeakageCore K A).range = ⊤ :=
    LinearMap.range_eq_top.mpr
      (modelSpaceLeakageCore_surjective_of_finiteDimensional K A hinj)
  exact LinearEquiv.finrank_eq (LinearEquiv.ofTop _ hrange)

/-- A dense leakage channel into an infinite-dimensional model space has infinite algebraic rank. -/
theorem not_finiteDimensional_range_modelSpaceLeakageCore
    (K : Submodule ℂ H) [K.HasOrthogonalProjection] [CompleteSpace K]
    (A : H →L[ℂ] H) (hK : ¬ FiniteDimensional ℂ K)
    (hinj : Function.Injective (A.adjoint.toLinearMap.domRestrict K)) :
    ¬ FiniteDimensional ℂ (modelSpaceLeakageCore K A).range := by
  intro hrange
  let T := modelSpaceLeakageCore K A
  have hTdense : DenseRange T := denseRange_modelSpaceLeakageCore K A hinj
  have hsubdense : Dense (((T.range : Submodule ℂ K) : Set K)) := by
    rw [show (((T.range : Submodule ℂ K) : Set K)) = Set.range T by
      ext y
      simp [LinearMap.mem_range, Set.mem_range]]
    exact hTdense
  letI : FiniteDimensional ℂ T.range := hrange
  have hclosureTop : T.range.topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp hsubdense
  have hclosureSelf : T.range.topologicalClosure = T.range :=
    Submodule.topologicalClosure_eq_self T.range
  have hrangeTop : T.range = ⊤ := hclosureSelf.symm.trans hclosureTop
  apply hK
  letI : FiniteDimensional ℂ (⊤ : Submodule ℂ K) := by
    rw [← hrangeTop]
    exact hrange
  let f : K →ₗ[ℂ] (⊤ : Submodule ℂ K) :=
    { toFun := fun x => ⟨x, Submodule.mem_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact FiniteDimensional.of_injective f (fun _ _ h => Subtype.ext_iff.mp h)

end

end GaloisForLFunctions.HTGeometry
