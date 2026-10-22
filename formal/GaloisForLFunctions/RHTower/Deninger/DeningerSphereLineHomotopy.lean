import GaloisForLFunctions.RHTower.Deninger.DeningerSphereSlideHomotopy

/-!
# The normalized straight-line homotopy on the unit sphere

If a linear isometry has no eigenvector, the segment from a unit vector to its image never meets
the origin, so normalizing it gives a homotopy on the sphere from the identity to the isometry.

* `deningerSphereLineHomotopy` : the homotopy from the identity of the sphere to the isometry.
-/

namespace RHTower

open scoped InnerProductSpace unitInterval

section LineHomotopy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The segment from `x` to `S x`, as a function of the parameter and the point. -/
noncomputable def deningerSegment (S : H →ₗᵢ[ℝ] H) (p : I × Metric.sphere (0 : H) 1) : H :=
  (1 - (p.1 : ℝ)) • (p.2 : H) + ((p.1 : ℝ)) • S ((p.2 : H))

theorem deningerSegment_continuous (S : H →ₗᵢ[ℝ] H) :
    Continuous (deningerSegment S) := by
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)
  · exact (continuous_subtype_val.comp continuous_fst).smul
      (S.continuous.comp (continuous_subtype_val.comp continuous_snd))

theorem deningerSegment_ne_zero (S : H →ₗᵢ[ℝ] H)
    (hS : ∀ (y : H) (c : ℝ), y ≠ 0 → S y ≠ c • y) (p : I × Metric.sphere (0 : H) 1) :
    deningerSegment S p ≠ 0 :=
  deningerSphereLine_ne_zero S hS (mem_sphere_zero_iff_norm.mp p.2.2) p.1.2.1 p.1.2.2

/-- **The normalized straight-line homotopy.**  It deforms the identity of the unit sphere to the
isometry `S`, along segments normalized to unit length. -/
noncomputable def deningerSphereLineHomotopy (S : H →ₗᵢ[ℝ] H)
    (hS : ∀ (y : H) (c : ℝ), y ≠ 0 → S y ≠ c • y) :
    ContinuousMap.Homotopy (ContinuousMap.id (Metric.sphere (0 : H) 1))
      (deningerSphereIsometryMap S) where
  toFun p := ⟨‖deningerSegment S p‖⁻¹ • deningerSegment S p, by
    have hne := deningerSegment_ne_zero S hS p
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.smul ?_ (deningerSegment_continuous S)
    exact ((deningerSegment_continuous S).norm).inv₀ fun p =>
      norm_ne_zero_iff.mpr (deningerSegment_ne_zero S hS p)
  map_zero_left x := by
    refine Subtype.ext ?_
    have hseg : deningerSegment S (0, x) = (x : H) := by
      show (1 - (0 : ℝ)) • (x : H) + (0 : ℝ) • S (x : H) = (x : H)
      rw [zero_smul, add_zero, sub_zero, one_smul]
    show ‖deningerSegment S (0, x)‖⁻¹ • deningerSegment S (0, x) = (x : H)
    rw [hseg, mem_sphere_zero_iff_norm.mp x.2, inv_one, one_smul]
  map_one_left x := by
    refine Subtype.ext ?_
    have hseg : deningerSegment S (1, x) = S (x : H) := by
      show (1 - (1 : ℝ)) • (x : H) + (1 : ℝ) • S (x : H) = S (x : H)
      rw [one_smul, sub_self, zero_smul, zero_add]
    show ‖deningerSegment S (1, x)‖⁻¹ • deningerSegment S (1, x) = S (x : H)
    rw [hseg, S.norm_map, mem_sphere_zero_iff_norm.mp x.2, inv_one, one_smul]

end LineHomotopy

end RHTower
