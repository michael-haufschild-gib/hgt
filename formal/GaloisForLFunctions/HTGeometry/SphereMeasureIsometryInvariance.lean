/-
# The unit-sphere measure is invariant under linear isometries

The sphere measure is the radial disintegration of the ambient Haar measure: a measurable set of
directions has sphere measure `dim E` times the ambient measure of the punctured cone it spans
inside the unit ball.  A linear isometry preserves the ambient measure, maps the unit sphere to
itself and commutes with the dilations that build the cone, so it preserves the sphere measure.

Main results:
* `sphereMap` — a linear isometry restricted to the unit sphere.
* `coe_image_preimage_sphereMap`, `smul_preimage_linearIsometryEquiv` — the two set identities.
* `measurePreserving_sphereMap` — **the sphere measure is invariant under linear isometries**.
-/
import Mathlib

open MeasureTheory Metric Set
open scoped Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

/-- A linear isometry of `E`, restricted to the unit sphere. -/
def sphereMap (f : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨f x, by
    rw [mem_sphere_zero_iff_norm, f.norm_map]
    exact mem_sphere_zero_iff_norm.mp x.2⟩

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem coe_sphereMap (f : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    ((sphereMap f x : sphere (0 : E) 1) : E) = f x := rfl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem continuous_sphereMap (f : E ≃ₗᵢ[ℝ] E) : Continuous (sphereMap f) :=
  Continuous.subtype_mk (f.continuous.comp continuous_subtype_val) _

omit [FiniteDimensional ℝ E] in
theorem measurable_sphereMap (f : E ≃ₗᵢ[ℝ] E) : Measurable (sphereMap f) :=
  (continuous_sphereMap f).measurable

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The cone spanned by the preimage of a set of directions is the preimage of its cone. -/
theorem coe_image_preimage_sphereMap (f : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0 : E) 1)) :
    (Subtype.val '' (sphereMap f ⁻¹' s)) = f ⁻¹' (Subtype.val '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨sphereMap f y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have hx : x ∈ sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, ← f.norm_map x, ← hzx]
      exact mem_sphere_zero_iff_norm.mp z.2
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    have hzeq : sphereMap f ⟨x, hx⟩ = z := Subtype.ext (by rw [coe_sphereMap]; exact hzx.symm)
    rw [Set.mem_preimage, hzeq]
    exact hz

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A linear isometry commutes with dilation of sets. -/
private theorem smul_preimage_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] E) (I : Set ℝ) (A : Set E) :
    I • (f ⁻¹' A) = f ⁻¹' (I • A) := by
  ext y
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    exact ⟨r, hr, f x, hx, by rw [map_smul]⟩
  · rintro ⟨r, hr, a, ha, hfa⟩
    have hfa' : r • a = f y := hfa
    refine ⟨r, hr, f.symm a, ?_, ?_⟩
    · rw [Set.mem_preimage, f.apply_symm_apply]
      exact ha
    · have hkey : f (r • f.symm a) = f y := by
        rw [map_smul, f.apply_symm_apply, hfa']
      exact f.injective hkey

theorem measure_preimage_linearIsometryEquiv (f : E ≃ₗᵢ[ℝ] E) (B : Set E) :
    (volume : Measure E) (f ⁻¹' B) = volume B := by
  have hmap : Measure.map (f : E → E) volume = (volume : Measure E) :=
    f.measurePreserving.map_eq
  have he := f.toHomeomorph.toMeasurableEquiv.map_apply (μ := (volume : Measure E)) B
  rw [show ⇑f.toHomeomorph.toMeasurableEquiv = (f : E → E) from rfl, hmap] at he
  exact he.symm

/-- **The unit-sphere measure is invariant under every linear isometry.** -/
theorem measurePreserving_sphereMap (f : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving (sphereMap f) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := by
  refine ⟨measurable_sphereMap f, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply (measurable_sphereMap f) hs,
    Measure.toSphere_apply' (μ := (volume : Measure E)) ((measurable_sphereMap f) hs),
    Measure.toSphere_apply' (μ := (volume : Measure E)) hs,
    coe_image_preimage_sphereMap f s, smul_preimage_linearIsometryEquiv f,
    measure_preimage_linearIsometryEquiv f]

/-- A linear isometry as a measurable equivalence of the unit sphere. -/
def sphereEquiv (f : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 where
  toFun := sphereMap f
  invFun := sphereMap f.symm
  left_inv := fun x => Subtype.ext (by
    rw [coe_sphereMap, coe_sphereMap, f.symm_apply_apply])
  right_inv := fun x => Subtype.ext (by
    rw [coe_sphereMap, coe_sphereMap, f.apply_symm_apply])
  measurable_toFun := measurable_sphereMap f
  measurable_invFun := measurable_sphereMap f.symm

omit [FiniteDimensional ℝ E] in
theorem coe_sphereEquiv (f : E ≃ₗᵢ[ℝ] E) : ⇑(sphereEquiv f) = sphereMap f := rfl

/-- **Integrals over the unit sphere are invariant under linear isometries.** -/
theorem integral_comp_sphereMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₗᵢ[ℝ] E) (g : sphere (0 : E) 1 → F) :
    (∫ x, g (sphereMap f x) ∂(volume : Measure E).toSphere)
      = ∫ x, g x ∂(volume : Measure E).toSphere := by
  have hmp : MeasurePreserving (sphereEquiv f) (volume : Measure E).toSphere
      (volume : Measure E).toSphere := measurePreserving_sphereMap f
  exact hmp.integral_comp' g

end

end GaloisForLFunctions.HTGeometry
