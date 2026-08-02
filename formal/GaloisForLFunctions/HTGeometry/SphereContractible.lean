import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Homotopy.Contractible

/-!
# The unit sphere of a space with a proper isometry is contractible

If a real inner product space carries a linear isometry `S` whose range is orthogonal to a unit
vector `e`, and which sends no nonzero vector to its negative, then the unit sphere is contractible:
the straight line from the identity to `S`, renormalised, never passes through the origin — a
vanishing point would force the parameter to be `1/2` and `S x = -x` — and the straight line from
`S` to the constant `e` never does either, because pairing with `e` detects it.

This is the contraction of the angular factor of a polar decomposition: the sphere of an
infinite-dimensional space is contractible, in contrast with the finite-dimensional case.

* `sphereUnit` : normalisation of a nonzero vector.
* `sphereIsometryMap` : a linear isometry as a self-map of the sphere.
* `contractibleSpace_sphere_of_isometry` : **the unit sphere is contractible.**
-/

open scoped InnerProductSpace unitInterval

noncomputable section

namespace GaloisForLFunctions

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Normalisation -/

theorem norm_inv_smul_mem_sphere {u : H} (hu : u ≠ 0) :
    ‖u‖⁻¹ • u ∈ Metric.sphere (0 : H) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

/-- The normalisation of a nonzero vector, as a point of the unit sphere. -/
def sphereUnit {u : H} (hu : u ≠ 0) : Metric.sphere (0 : H) 1 :=
  ⟨‖u‖⁻¹ • u, norm_inv_smul_mem_sphere hu⟩

theorem sphereUnit_of_norm_one {u : H} (hu : u ≠ 0) (h1 : ‖u‖ = 1) :
    (sphereUnit hu : H) = u := by
  show ‖u‖⁻¹ • u = u
  rw [h1, inv_one, one_smul]

/-! ## The isometry as a map of the sphere -/

variable (S : H →ₗᵢ[ℝ] H)

theorem norm_isometry_sphere (x : Metric.sphere (0 : H) 1) : ‖S (x : H)‖ = 1 := by
  rw [S.norm_map]
  exact mem_sphere_zero_iff_norm.mp x.2

/-- A linear isometry as a self-map of the unit sphere. -/
def sphereIsometryMap : C(Metric.sphere (0 : H) 1, Metric.sphere (0 : H) 1) where
  toFun x := ⟨S (x : H), by
    rw [mem_sphere_zero_iff_norm]
    exact norm_isometry_sphere S x⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact S.continuous.comp continuous_subtype_val

/-! ## The two straight-line families are nonvanishing -/

theorem lineToIsometry_ne_zero (hfix : ∀ x : H, S x = -x → x = 0) (t : I)
    (x : Metric.sphere (0 : H) 1) :
    (1 - (t : ℝ)) • (x : H) + (t : ℝ) • S (x : H) ≠ 0 := by
  intro hzero
  have hx1 : ‖(x : H)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hSx1 : ‖S (x : H)‖ = 1 := norm_isometry_sphere S x
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have heq : (1 - (t : ℝ)) • (x : H) = -((t : ℝ) • S (x : H)) := by
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact hzero
  have hnorm : (1 - (t : ℝ)) * ‖(x : H)‖ = (t : ℝ) * ‖S (x : H)‖ := by
    have h1 : ‖(1 - (t : ℝ)) • (x : H)‖ = ‖-((t : ℝ) • S (x : H))‖ := by rw [heq]
    rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (t : ℝ)), abs_of_nonneg ht0] at h1
    exact h1
  rw [hx1, hSx1, mul_one, mul_one] at hnorm
  have hthalf : (t : ℝ) = 1 / 2 := by linarith
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hthalf, hhalf] at hzero
  have h2 : (1 / 2 : ℝ) • ((x : H) + S (x : H)) = 0 := by
    rw [smul_add]
    exact hzero
  have h4 : (x : H) + S (x : H) = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hxS : S (x : H) = -(x : H) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h4
  have hx0 : (x : H) = 0 := hfix (x : H) hxS
  rw [hx0, norm_zero] at hx1
  exact absurd hx1 (by norm_num)

theorem lineToPoint_ne_zero {e : H} (he : ‖e‖ = 1) (hperp : ∀ x : H, ⟪S x, e⟫_ℝ = 0) (t : I)
    (x : Metric.sphere (0 : H) 1) :
    (1 - (t : ℝ)) • S (x : H) + (t : ℝ) • e ≠ 0 := by
  intro hzero
  have hinner : ⟪(1 - (t : ℝ)) • S (x : H) + (t : ℝ) • e, e⟫_ℝ = (t : ℝ) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hperp (x : H),
      real_inner_self_eq_norm_sq, he]
    ring
  rw [hzero, inner_zero_left] at hinner
  have ht : (t : ℝ) = 0 := hinner.symm
  have hSx : ‖S (x : H)‖ = 1 := norm_isometry_sphere S x
  rw [ht] at hzero
  simp only [sub_zero, one_smul, zero_smul, add_zero] at hzero
  rw [hzero, norm_zero] at hSx
  exact absurd hSx (by norm_num)

/-! ## The contraction -/

/-- The renormalised straight line from the identity to the isometry. -/
def sphereHomotopyToIsometry (hfix : ∀ x : H, S x = -x → x = 0) :
    (ContinuousMap.id (Metric.sphere (0 : H) 1)).Homotopy (sphereIsometryMap S) where
  toFun p := sphereUnit (lineToIsometry_ne_zero S hfix p.1 p.2)
  continuous_toFun := by
    have hu : Continuous fun p : I × Metric.sphere (0 : H) 1 =>
        (1 - (p.1 : ℝ)) • (p.2 : H) + (p.1 : ℝ) • S (p.2 : H) := by
      fun_prop
    refine Continuous.subtype_mk ?_ _
    refine Continuous.smul ?_ hu
    refine (continuous_norm.comp hu).inv₀ ?_
    intro p
    exact norm_ne_zero_iff.mpr (lineToIsometry_ne_zero S hfix p.1 p.2)
  map_zero_left x := by
    refine Subtype.ext ?_
    have hval : (1 - ((0 : I) : ℝ)) • (x : H) + ((0 : I) : ℝ) • S (x : H) = (x : H) := by
      norm_num
    have h1 : ‖(1 - ((0 : I) : ℝ)) • (x : H) + ((0 : I) : ℝ) • S (x : H)‖ = 1 := by
      rw [hval]
      exact mem_sphere_zero_iff_norm.mp x.2
    rw [sphereUnit_of_norm_one _ h1, hval]
    rfl
  map_one_left x := by
    refine Subtype.ext ?_
    have hval : (1 - ((1 : I) : ℝ)) • (x : H) + ((1 : I) : ℝ) • S (x : H) = S (x : H) := by
      norm_num
    have h1 : ‖(1 - ((1 : I) : ℝ)) • (x : H) + ((1 : I) : ℝ) • S (x : H)‖ = 1 := by
      rw [hval]
      exact norm_isometry_sphere S x
    rw [sphereUnit_of_norm_one _ h1, hval]
    rfl

/-- The renormalised straight line from the isometry to the base point. -/
def sphereHomotopyToPoint {e : H} (he : ‖e‖ = 1) (hperp : ∀ x : H, ⟪S x, e⟫_ℝ = 0) :
    (sphereIsometryMap S).Homotopy
      (ContinuousMap.const (Metric.sphere (0 : H) 1)
        (⟨e, by rw [mem_sphere_zero_iff_norm]; exact he⟩ : Metric.sphere (0 : H) 1)) where
  toFun p := sphereUnit (lineToPoint_ne_zero S he hperp p.1 p.2)
  continuous_toFun := by
    have hu : Continuous fun p : I × Metric.sphere (0 : H) 1 =>
        (1 - (p.1 : ℝ)) • S (p.2 : H) + (p.1 : ℝ) • e := by
      fun_prop
    refine Continuous.subtype_mk ?_ _
    refine Continuous.smul ?_ hu
    refine (continuous_norm.comp hu).inv₀ ?_
    intro p
    exact norm_ne_zero_iff.mpr (lineToPoint_ne_zero S he hperp p.1 p.2)
  map_zero_left x := by
    refine Subtype.ext ?_
    have hval : (1 - ((0 : I) : ℝ)) • S (x : H) + ((0 : I) : ℝ) • e = S (x : H) := by
      norm_num
    have h1 : ‖(1 - ((0 : I) : ℝ)) • S (x : H) + ((0 : I) : ℝ) • e‖ = 1 := by
      rw [hval]
      exact norm_isometry_sphere S x
    rw [sphereUnit_of_norm_one _ h1, hval]
    rfl
  map_one_left x := by
    refine Subtype.ext ?_
    have hval : (1 - ((1 : I) : ℝ)) • S (x : H) + ((1 : I) : ℝ) • e = e := by
      norm_num
    have h1 : ‖(1 - ((1 : I) : ℝ)) • S (x : H) + ((1 : I) : ℝ) • e‖ = 1 := by
      rw [hval]
      exact he
    rw [sphereUnit_of_norm_one _ h1, hval]
    rfl

/-- **The unit sphere is contractible** when the space carries a linear isometry whose range misses
a unit vector orthogonally and which fixes no antipode. -/
theorem contractibleSpace_sphere_of_isometry {e : H} (he : ‖e‖ = 1)
    (hperp : ∀ x : H, ⟪S x, e⟫_ℝ = 0) (hfix : ∀ x : H, S x = -x → x = 0) :
    ContractibleSpace (Metric.sphere (0 : H) 1) := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨e, by rw [mem_sphere_zero_iff_norm]; exact he⟩, ?_⟩
  exact ⟨(sphereHomotopyToIsometry S hfix).trans (sphereHomotopyToPoint S he hperp)⟩

end GaloisForLFunctions

end
