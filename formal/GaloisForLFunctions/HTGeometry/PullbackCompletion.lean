import GaloisForLFunctions.HTGeometry.SelfAdjointResolvent

/-!
# The pullback completion of a linear map into a Hilbert space

Give the quotient of a vector space by the kernel of a linear map into a Hilbert space the norm
of the image.  The induced map onto the range is then a bijective isometry, the range is dense in
its closure, and that closure is complete.  So the completion in the pullback norm is exactly the
closure of the range: the pullback completion is a closed subspace of the ambient Hilbert space.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {D K : Type*} [AddCommGroup D] [Module ℂ D]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The pullback space of a linear map into a Hilbert space: the closure of its range. -/
def pullbackSpace (Δ : D →ₗ[ℂ] K) : Submodule ℂ K := (LinearMap.range Δ).topologicalClosure

omit [CompleteSpace K] in
theorem isClosed_pullbackSpace (Δ : D →ₗ[ℂ] K) :
    IsClosed ((pullbackSpace Δ : Submodule ℂ K) : Set K) :=
  Submodule.isClosed_topologicalClosure _

instance completeSpace_pullbackSpace (Δ : D →ₗ[ℂ] K) : CompleteSpace (pullbackSpace Δ) := by
  haveI : IsClosed ((pullbackSpace Δ : Submodule ℂ K) : Set K) := isClosed_pullbackSpace Δ
  exact IsClosed.completeSpace_coe

/-- The pullback norm `‖[f]‖_η = ‖Δ f‖` on the quotient by the kernel. -/
def pullbackNorm (Δ : D →ₗ[ℂ] K) (q : D ⧸ LinearMap.ker Δ) : ℝ :=
  ‖((Δ.quotKerEquivRange q : LinearMap.range Δ) : K)‖

omit [CompleteSpace K] in
@[simp] theorem pullbackNorm_mk (Δ : D →ₗ[ℂ] K) (f : D) :
    pullbackNorm Δ (Submodule.Quotient.mk f) = ‖Δ f‖ := by
  rw [pullbackNorm, LinearMap.quotKerEquivRange_apply_mk]

/-- The descent of `Δ` to the quotient by its kernel, landing in the pullback space. -/
def pullbackEmbedding (Δ : D →ₗ[ℂ] K) : (D ⧸ LinearMap.ker Δ) →ₗ[ℂ] pullbackSpace Δ :=
  (Submodule.inclusion ((LinearMap.range Δ).le_topologicalClosure)).comp
    Δ.quotKerEquivRange.toLinearMap

omit [CompleteSpace K] in
@[simp] theorem pullbackEmbedding_coe (Δ : D →ₗ[ℂ] K) (q : D ⧸ LinearMap.ker Δ) :
    ((pullbackEmbedding Δ q : pullbackSpace Δ) : K) =
      ((Δ.quotKerEquivRange q : LinearMap.range Δ) : K) := rfl

omit [CompleteSpace K] in
@[simp] theorem pullbackEmbedding_mk (Δ : D →ₗ[ℂ] K) (f : D) :
    ((pullbackEmbedding Δ (Submodule.Quotient.mk f) : pullbackSpace Δ) : K) = Δ f := by
  rw [pullbackEmbedding_coe, LinearMap.quotKerEquivRange_apply_mk]

omit [CompleteSpace K] in
/-- **The pullback embedding is isometric for the pullback norm.** -/
theorem norm_pullbackEmbedding (Δ : D →ₗ[ℂ] K) (q : D ⧸ LinearMap.ker Δ) :
    ‖pullbackEmbedding Δ q‖ = pullbackNorm Δ q := rfl

omit [CompleteSpace K] in
/-- **The pullback embedding is injective.** -/
theorem injective_pullbackEmbedding (Δ : D →ₗ[ℂ] K) :
    Function.Injective (pullbackEmbedding Δ) := by
  intro a b hab
  have : (Δ.quotKerEquivRange a : LinearMap.range Δ) = Δ.quotKerEquivRange b :=
    Subtype.ext (congrArg (fun v : pullbackSpace Δ => (v : K)) hab)
  exact Δ.quotKerEquivRange.injective this

omit [CompleteSpace K] in
theorem range_pullbackEmbedding_coe (Δ : D →ₗ[ℂ] K) :
    (Set.range fun q => ((pullbackEmbedding Δ q : pullbackSpace Δ) : K)) =
      (LinearMap.range Δ : Set K) := by
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    exact (Δ.quotKerEquivRange q).2
  · rintro ⟨f, rfl⟩
    exact ⟨Submodule.Quotient.mk f, pullbackEmbedding_mk Δ f⟩

omit [CompleteSpace K] in
/-- **The pullback embedding has dense image in the pullback space.**  Together with completeness
of the pullback space this says that the completion in the pullback norm is exactly the closure of
the range: the pullback completion is a closed subspace of the ambient Hilbert space. -/
theorem closure_range_pullbackEmbedding (Δ : D →ₗ[ℂ] K) :
    closure (Set.range fun q => ((pullbackEmbedding Δ q : pullbackSpace Δ) : K)) =
      (pullbackSpace Δ : Set K) := by
  rw [range_pullbackEmbedding_coe]
  rfl

end GaloisForLFunctions.HTGeometry
