import GaloisForLFunctions.RHTower.DeningerSphereContraction
import Mathlib.Topology.Homotopy.Basic

/-!
# The quarter-circle homotopy on the unit sphere

The deformation `x ↦ √(1 - t²)·S x + t·e` is a homotopy on the unit sphere from the isometry `S`
to the constant `e`, whenever `e` is a unit vector orthogonal to the range of `S`.

* `deningerSphereIsometryMap` : the isometry as a self-map of the sphere.
* `deningerSlideHomotopy` : the homotopy from it to the constant map.
-/

namespace RHTower

open scoped InnerProductSpace unitInterval

section SlideHomotopy

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A linear isometry restricts to a self-map of the unit sphere. -/
noncomputable def deningerSphereIsometryMap (S : H →ₗᵢ[ℝ] H) :
    C(Metric.sphere (0 : H) 1, Metric.sphere (0 : H) 1) where
  toFun x := ⟨S (x : H), by
    rw [mem_sphere_zero_iff_norm, S.norm_map, ← mem_sphere_zero_iff_norm]
    exact x.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact S.continuous.comp continuous_subtype_val

/-- The constant map at a unit vector. -/
noncomputable def deningerSphereConstMap {e : H} (he : ‖e‖ = 1) :
    C(Metric.sphere (0 : H) 1, Metric.sphere (0 : H) 1) :=
  ContinuousMap.const _ ⟨e, mem_sphere_zero_iff_norm.mpr he⟩

/-- **The quarter-circle homotopy.**  It deforms the isometry `S`, viewed on the unit sphere, to
the constant map at a unit vector orthogonal to its range. -/
noncomputable def deningerSlideHomotopy (S : H →ₗᵢ[ℝ] H) {e : H} (he : ‖e‖ = 1)
    (hperp : ∀ y : H, ⟪S y, e⟫_ℝ = 0) :
    ContinuousMap.Homotopy (deningerSphereIsometryMap S) (deningerSphereConstMap he) where
  toFun p := ⟨Real.sqrt (1 - ((p.1 : ℝ)) ^ (2 : ℕ)) • S ((p.2 : H)) + ((p.1 : ℝ)) • e, by
    rw [mem_sphere_zero_iff_norm]
    exact deningerSphereSlide_norm S he hperp (mem_sphere_zero_iff_norm.mp p.2.2)
      p.1.2.1 p.1.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.add ?_ ?_
    · refine Continuous.smul ?_ ?_
      · exact (Real.continuous_sqrt.comp
          ((continuous_const.sub ((continuous_subtype_val.comp continuous_fst).pow 2))))
      · exact S.continuous.comp (continuous_subtype_val.comp continuous_snd)
    · exact (continuous_subtype_val.comp continuous_fst).smul continuous_const
  map_zero_left x := by
    refine Subtype.ext ?_
    show Real.sqrt (1 - (0 : ℝ) ^ (2 : ℕ)) • S ((x : H)) + (0 : ℝ) • e = S (x : H)
    rw [zero_smul, add_zero]
    norm_num
  map_one_left x := by
    refine Subtype.ext ?_
    show Real.sqrt (1 - (1 : ℝ) ^ (2 : ℕ)) • S ((x : H)) + (1 : ℝ) • e = e
    rw [one_smul]
    norm_num

end SlideHomotopy

end RHTower
