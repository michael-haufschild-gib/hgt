import GaloisForLFunctions.HTGeometry.ClosedSubgroupLineStructure
import Mathlib.Analysis.Complex.Basic

/-!
# Closed planar subgroups with a nonreal multiplier

A real line and its image under a nonreal complex multiplier span the
plane. Consequently a closed additive subgroup preserved by that
multiplier is either discrete at the origin or the whole plane.
For triangular lattices the multiplier is a primitive cube root of unity;
for square lattices it is `i`.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric

open HTGeometry Set

/-- A nonreal multiplier turns one nonzero real line in a subgroup into the full plane. -/
theorem subgroup_eq_top_of_nonreal_mul_line (H : AddSubgroup ℂ) (w : ℂ)
    (hw : w.im ≠ 0) (hmul : ∀ z ∈ H, w * z ∈ H)
    (u : ℂ) (hu : u ≠ 0) (hline : ∀ t : ℝ, t • u ∈ H) : H = ⊤ := by
  apply top_unique
  intro z _
  let b : ℝ := (z / u).im / w.im
  let a : ℝ := (z / u).re - b * w.re
  have hcoords : z / u = (a : ℂ) + (b : ℂ) * w := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      dsimp [a]
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_add]
      dsimp [b]
      field_simp
  have hdecomp : z = a • u + w * (b • u) := by
    have h := congrArg (fun q : ℂ => q * u) hcoords
    rw [div_mul_cancel₀ z hu] at h
    rw [h]
    simp only [Complex.real_smul]
    ring
  rw [hdecomp]
  exact H.add_mem (hline a) (hmul _ (hline b))

/-- A closed subgroup with a nonreal multiplier is discrete or fills the plane. -/
theorem closed_subgroup_nonreal_mul_dichotomy (H : AddSubgroup ℂ)
    (hH : IsClosed (H : Set ℂ)) (w : ℂ) (hw : w.im ≠ 0)
    (hmul : ∀ z ∈ H, w * z ∈ H) :
    H = ⊤ ∨ ∃ ε > 0, ∀ z ∈ H, ‖z‖ < ε → z = 0 := by
  by_cases htop : H = ⊤
  · exact Or.inl htop
  · right
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_forall_mem_lineDirections hH
    refine ⟨ε, hε, fun z hz hnorm => ?_⟩
    by_contra hz0
    exact htop (subgroup_eq_top_of_nonreal_mul_line H w hw hmul z hz0
      (hsmall z hz hnorm))

/-- For a proper closed subgroup, rotation symmetry forces a positive separation scale. -/
theorem separated_of_closed_subgroup_nonreal_mul (H : AddSubgroup ℂ)
    (hH : IsClosed (H : Set ℂ)) (w : ℂ) (hw : w.im ≠ 0)
    (hmul : ∀ z ∈ H, w * z ∈ H) (hproper : H ≠ ⊤) :
    ∃ ε > 0, ∀ x ∈ H, ∀ y ∈ H, x ≠ y → ε ≤ dist x y := by
  obtain ⟨ε, hε, hsmall⟩ :=
    (closed_subgroup_nonreal_mul_dichotomy H hH w hw hmul).resolve_left hproper
  refine ⟨ε, hε, fun x hx y hy hxy => ?_⟩
  by_contra h
  have hzero := hsmall (x - y) (H.sub_mem hx hy) (by
    simpa only [dist_eq_norm, not_le] using h)
  exact hxy (sub_eq_zero.mp hzero)

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.subgroup_eq_top_of_nonreal_mul_line
#print axioms GaloisForLFunctions.HilbertMetric.closed_subgroup_nonreal_mul_dichotomy
#print axioms GaloisForLFunctions.HilbertMetric.separated_of_closed_subgroup_nonreal_mul
