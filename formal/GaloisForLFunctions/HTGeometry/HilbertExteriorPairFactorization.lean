import GaloisForLFunctions.HTGeometry.BilinearExteriorPairFactorization
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Exterior factorization of difference-weighted Hilbert tensor pair sections

The bilinear exterior identity holds for the continuous tensor map `TensorProduct.mapL` of Hilbert
spaces, because `mapL` is additive and homogeneous in each argument.  Packaging it as a bilinear
map of the two operator spaces gives

`∑_i ∑_j (a i − a j) • mapL (C i) (C j) = mapL (∑ a i • C i) (∑ C j) − mapL (∑ C i) (∑ a j • C j)`

over any finite index set, so a difference-weighted ordered pair section of Hilbert-space operators
is a decomposable rank-two exterior tensor of two one-particle sections.
-/

open scoped TensorProduct

namespace HTGeometry

section HilbertBilinear

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- `TensorProduct.mapL` as a bilinear map of the two operator spaces. -/
noncomputable def mapLBilinear :
    (E →L[𝕜] F) →ₗ[𝕜] (G →L[𝕜] H) →ₗ[𝕜] ((E ⊗[𝕜] G) →L[𝕜] (F ⊗[𝕜] H)) where
  toFun f :=
    { toFun := fun g => TensorProduct.mapL f g
      map_add' := fun g₁ g₂ => TensorProduct.mapL_add_right f g₁ g₂
      map_smul' := fun r g => TensorProduct.mapL_smul_right r f g }
  map_add' f₁ f₂ := LinearMap.ext fun g => TensorProduct.mapL_add_left f₁ f₂ g
  map_smul' r f := LinearMap.ext fun g => TensorProduct.mapL_smul_left r f g

@[simp] theorem mapLBilinear_apply (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLBilinear f g = TensorProduct.mapL f g := rfl

end HilbertBilinear

section FinsetBilinear

variable {R M N P ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- **Exterior pair factorization over a finite index set.**  The double sum weighted by the
coefficient difference collapses to the exterior combination of the two one-particle sections. -/
theorem sum_sub_smul_bilinear_finset (s : Finset ι) (B : M →ₗ[R] N →ₗ[R] P) (a : ι → R)
    (C : ι → M) (D : ι → N) :
    ∑ i ∈ s, ∑ j ∈ s, (a i - a j) • B (C i) (D j)
      = B (∑ i ∈ s, a i • C i) (∑ j ∈ s, D j) - B (∑ i ∈ s, C i) (∑ j ∈ s, a j • D j) := by
  have hrow : ∀ i ∈ s, ∑ j ∈ s, (a i - a j) • B (C i) (D j)
      = (B (a i • C i)) (∑ j ∈ s, D j) - (B (C i)) (∑ j ∈ s, a j • D j) := by
    intro i _
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_smul, map_smul, LinearMap.smul_apply, map_smul]
  have h1 : ∑ i ∈ s, (B (a i • C i)) (∑ j ∈ s, D j)
      = (B (∑ i ∈ s, a i • C i)) (∑ j ∈ s, D j) := by
    rw [map_sum B (fun i => a i • C i) s, LinearMap.sum_apply]
  have h2 : ∑ i ∈ s, (B (C i)) (∑ j ∈ s, a j • D j)
      = (B (∑ i ∈ s, C i)) (∑ j ∈ s, a j • D j) := by
    rw [map_sum B (fun i => C i) s, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, h1, h2]

end FinsetBilinear

section HilbertExterior

variable {𝕜 E F ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **The difference-weighted ordered Hilbert pair section is a decomposable exterior tensor.** -/
theorem sum_sub_smul_mapL (s : Finset ι) (a : ι → 𝕜) (C : ι → (E →L[𝕜] F)) :
    ∑ i ∈ s, ∑ j ∈ s, (a i - a j) • TensorProduct.mapL (C i) (C j)
      = TensorProduct.mapL (∑ i ∈ s, a i • C i) (∑ j ∈ s, C j)
        - TensorProduct.mapL (∑ i ∈ s, C i) (∑ j ∈ s, a j • C j) := by
  have h := sum_sub_smul_bilinear_finset (R := 𝕜) s
    (mapLBilinear (𝕜 := 𝕜) (E := E) (F := F) (G := E) (H := F)) a C C
  simpa only [mapLBilinear_apply] using h

end HilbertExterior

end HTGeometry
