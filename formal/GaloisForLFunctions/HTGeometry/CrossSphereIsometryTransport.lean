/-
# Transporting the spherical measure along a linear isometry

A linear isometry equivalence of finite-dimensional inner product spaces restricts to a bijection of
the unit spheres, commutes with dilation of sets, and preserves volume, so the cone presentation of
the spherical measure transports: the sphere measure of a set equals the sphere measure of its
preimage.

Main results:
* `crossSphereMap` — the restriction of a linear isometry equivalence to the unit spheres.
* `toSphere_preimage_crossSphereMap` — **the spherical measure is transported**.
-/
import Mathlib

open MeasureTheory Metric Set
open scoped Pointwise

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence restricted to the unit spheres. -/
def crossSphereMap (T : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 ≃ sphere (0 : F) 1 where
  toFun x := ⟨T (x : E), by
    rw [mem_sphere_iff_norm, sub_zero, T.norm_map]
    have := x.2
    rw [mem_sphere_iff_norm, sub_zero] at this
    exact this⟩
  invFun y := ⟨T.symm (y : F), by
    rw [mem_sphere_iff_norm, sub_zero, T.symm.norm_map]
    have := y.2
    rw [mem_sphere_iff_norm, sub_zero] at this
    exact this⟩
  left_inv x := by
    refine Subtype.ext ?_
    exact T.symm_apply_apply (x : E)
  right_inv y := by
    refine Subtype.ext ?_
    exact T.apply_symm_apply (y : F)

theorem continuous_crossSphereMap (T : E ≃ₗᵢ[ℝ] F) : Continuous (crossSphereMap T) :=
  Continuous.subtype_mk (T.continuous.comp continuous_subtype_val) _

theorem image_crossSphereMap_preimage (T : E ≃ₗᵢ[ℝ] F) (S : Set (sphere (0 : F) 1)) :
    (T : E → F) '' (Subtype.val '' (crossSphereMap T ⁻¹' S)) = Subtype.val '' S := by
  ext y
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨crossSphereMap T w, hw, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨((crossSphereMap T).symm u : E), ⟨(crossSphereMap T).symm u, ?_, rfl⟩, ?_⟩
    · show crossSphereMap T ((crossSphereMap T).symm u) ∈ S
      rw [Equiv.apply_symm_apply]
      exact hu
    · show T (((crossSphereMap T).symm u : E)) = (u : F)
      exact T.apply_symm_apply (u : F)

theorem image_smul_set_isometry (T : E ≃ₗᵢ[ℝ] F) (I : Set ℝ) (A : Set E) :
    (T : E → F) '' (I • A) = I • ((T : E → F) '' A) := by
  ext y
  constructor
  · rintro ⟨x, ⟨r, hr, u, hu, rfl⟩, rfl⟩
    exact ⟨r, hr, T u, ⟨u, hu, rfl⟩, by rw [T.map_smul]⟩
  · rintro ⟨r, hr, y', ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨r • u, ⟨r, hr, u, hu, rfl⟩, by rw [T.map_smul]⟩

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- **The spherical measure is transported by a linear isometry equivalence.** -/
theorem toSphere_preimage_crossSphereMap (T : E ≃ₗᵢ[ℝ] F) {S : Set (sphere (0 : F) 1)}
    (hS : MeasurableSet S) :
    (volume : Measure E).toSphere (crossSphereMap T ⁻¹' S)
      = (volume : Measure F).toSphere S := by
  have hpre : MeasurableSet (crossSphereMap T ⁻¹' S) :=
    hS.preimage (continuous_crossSphereMap T).measurable
  rw [Measure.toSphere_apply' _ hpre, Measure.toSphere_apply' _ hS]
  have hrank : Module.finrank ℝ E = Module.finrank ℝ F :=
    T.toLinearEquiv.finrank_eq
  rw [hrank]
  congr 1
  have hmp : MeasurePreserving (T : E → F) volume volume := T.measurePreserving
  have himg : (T : E → F) '' (Set.Ioo (0:ℝ) 1 • Subtype.val '' (crossSphereMap T ⁻¹' S))
      = Set.Ioo (0:ℝ) 1 • Subtype.val '' S := by
    rw [image_smul_set_isometry, image_crossSphereMap_preimage]
  have hpreimg : Set.Ioo (0:ℝ) 1 • Subtype.val '' (crossSphereMap T ⁻¹' S)
      = (T : E → F) ⁻¹' (Set.Ioo (0:ℝ) 1 • Subtype.val '' S) := by
    rw [← himg]
    exact (T.toEquiv.preimage_image _).symm
  rw [hpreimg]
  exact hmp.measure_preimage_emb (T.toHomeomorph.measurableEmbedding) _

end GaloisForLFunctions.HTGeometry

end
