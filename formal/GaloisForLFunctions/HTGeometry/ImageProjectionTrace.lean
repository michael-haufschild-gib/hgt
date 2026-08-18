import GaloisForLFunctions.HTGeometry.CoordinateInnerProductToolkit

/-!
# Transporting a projector along an invertible scaling

An invertible matrix carries the range of an orthogonal projector to a subspace of the same
dimension, and the orthogonal projector onto that image absorbs the scaled projector.  Since the
trace of an idempotent is the dimension of its range, the transported projector has the same trace
as the original: transporting a target subspace along an invertible normalization costs no
dimension.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The Euclidean linear map of a product is the composition. -/
theorem toEuclideanLin_mul (M N : Matrix X X ℂ) :
    Matrix.toEuclideanLin (M * N)
      = (Matrix.toEuclideanLin M).comp (Matrix.toEuclideanLin N) := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec]

/-- **The trace of an idempotent is the dimension of its range.** -/
theorem trace_eq_finrank_range (P : Matrix X X ℂ) (hPP : P * P = P) :
    Matrix.trace P = (Module.finrank ℂ (LinearMap.range (Matrix.toEuclideanLin P)) : ℂ) := by
  have hidem : IsIdempotentElem (Matrix.toEuclideanLin P) := by
    rw [IsIdempotentElem]
    show (Matrix.toEuclideanLin P).comp (Matrix.toEuclideanLin P) = Matrix.toEuclideanLin P
    rw [← toEuclideanLin_mul, hPP]
  have hproj := LinearMap.IsIdempotentElem.isProj_range _ hidem
  have htr : LinearMap.trace ℂ (EuclideanSpace ℂ X) (Matrix.toEuclideanLin P)
      = Matrix.trace P := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun X ℂ).toBasis]
    congr 1
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  rw [← htr]
  exact hproj.trace

/-- The Euclidean linear map of the identity is the identity. -/
theorem toEuclideanLin_one : Matrix.toEuclideanLin (1 : Matrix X X ℂ) = LinearMap.id := by
  ext x
  simp

/-- The linear equivalence attached to a two-sided matrix inverse pair. -/
def euclidEquivOfInv (R S : Matrix X X ℂ) (h1 : R * S = 1) (h2 : S * R = 1) :
    EuclideanSpace ℂ X ≃ₗ[ℂ] EuclideanSpace ℂ X :=
  LinearEquiv.ofLinear (Matrix.toEuclideanLin R) (Matrix.toEuclideanLin S)
    (by rw [← toEuclideanLin_mul, h1, toEuclideanLin_one])
    (by rw [← toEuclideanLin_mul, h2, toEuclideanLin_one])

/-- The transport equivalence acts by the matrix it was built from. -/
theorem euclidEquivOfInv_coe (R S : Matrix X X ℂ) (h1 : R * S = 1) (h2 : S * R = 1) :
    ((euclidEquivOfInv R S h1 h2 : EuclideanSpace ℂ X ≃ₗ[ℂ] EuclideanSpace ℂ X) :
      EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X) = Matrix.toEuclideanLin R := rfl

/-- The orthogonal projector onto the image of the range of a projector. -/
def imageProjection (R P : Matrix X X ℂ) : Matrix X X ℂ :=
  (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ)).symm
    (Submodule.starProjection
      (Submodule.map (Matrix.toEuclideanLin R) (LinearMap.range (Matrix.toEuclideanLin P))))

/-- The image projector acts as the orthogonal projection onto the transported range. -/
theorem imageProjection_apply (R P : Matrix X X ℂ) (x : EuclideanSpace ℂ X) :
    (imageProjection R P).toEuclideanLin x =
      Submodule.starProjection
        (Submodule.map (Matrix.toEuclideanLin R)
          (LinearMap.range (Matrix.toEuclideanLin P))) x := by
  change Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (imageProjection R P) x = _
  rw [imageProjection, StarAlgEquiv.apply_symm_apply]

/-- The image projector is self-adjoint. -/
theorem imageProjection_conjTranspose (R P : Matrix X X ℂ) :
    (imageProjection R P)ᴴ = imageProjection R P := by
  have hself := isSelfAdjoint_starProjection
    (Submodule.map (Matrix.toEuclideanLin R) (LinearMap.range (Matrix.toEuclideanLin P)))
  apply EquivLike.injective (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ))
  have hmapstar : Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) ((imageProjection R P)ᴴ)
      = star (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ) (imageProjection R P)) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact map_star _ _
  rw [hmapstar, imageProjection, StarAlgEquiv.apply_symm_apply]
  exact hself.star_eq

/-- The image projector is idempotent. -/
theorem imageProjection_mul_self (R P : Matrix X X ℂ) :
    imageProjection R P * imageProjection R P = imageProjection R P := by
  apply (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ)).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change (imageProjection R P).toEuclideanLin ((imageProjection R P).toEuclideanLin x) =
    (imageProjection R P).toEuclideanLin x
  rw [imageProjection_apply, imageProjection_apply]
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem _ x)

/-- The image projector fixes the scaled projector. -/
theorem imageProjection_mul (R P : Matrix X X ℂ) :
    imageProjection R P * (R * P) = R * P := by
  apply (Matrix.toEuclideanCLM (n := X) (𝕜 := ℂ)).injective
  rw [map_mul]
  apply ContinuousLinearMap.ext
  intro x
  change (imageProjection R P).toEuclideanLin ((R * P).toEuclideanLin x) =
    (R * P).toEuclideanLin x
  rw [imageProjection_apply]
  refine Submodule.starProjection_eq_self_iff.mpr ?_
  rw [toEuclideanLin_mul]
  exact ⟨(Matrix.toEuclideanLin P) x, ⟨x, rfl⟩, rfl⟩

/-- The complementary image projector annihilates the scaled projector. -/
theorem one_sub_imageProjection_mul (R P : Matrix X X ℂ) :
    (1 - imageProjection R P) * (R * P) = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, imageProjection_mul, sub_self]

/-- **Transport along an invertible scaling preserves the trace of a projector.** -/
theorem imageProjection_trace (R S P : Matrix X X ℂ) (h1 : R * S = 1) (h2 : S * R = 1)
    (hPP : P * P = P) :
    Matrix.trace (imageProjection R P) = Matrix.trace P := by
  set W := Submodule.map (Matrix.toEuclideanLin R) (LinearMap.range (Matrix.toEuclideanLin P))
    with hW
  have hrange : LinearMap.range (Matrix.toEuclideanLin (imageProjection R P)) = W := by
    have hcoe : Matrix.toEuclideanLin (imageProjection R P)
        = (W.starProjection : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X) := by
      ext x
      rw [imageProjection_apply]
      rfl
    rw [hcoe]
    exact Submodule.range_starProjection W
  rw [trace_eq_finrank_range _ (imageProjection_mul_self R P), trace_eq_finrank_range P hPP,
    hrange, hW]
  congr 1
  have hfr := LinearEquiv.finrank_map_eq (euclidEquivOfInv R S h1 h2)
    (LinearMap.range (Matrix.toEuclideanLin P))
  rw [euclidEquivOfInv_coe] at hfr
  rw [hfr]

end

end GaloisForLFunctions.HTGeometry
