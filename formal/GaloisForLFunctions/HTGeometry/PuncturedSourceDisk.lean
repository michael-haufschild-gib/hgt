import GaloisForLFunctions.HTGeometry.PuncturedDiskCover

/-!
# Connected punctured source neighborhoods

Affine normalization identifies every positive-radius punctured complex disk
with the punctured unit disk. Every punctured neighborhood contains one of
these connected open disks.
-/

open Topology Set Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Affine punctured source disks used to locate a lift in one peripheral component. -/
def puncturedSourceDisk (a : ℂ) (r : ℝ) : Set ℂ := {z | z ≠ a ∧ ‖z - a‖ < r}

theorem isOpen_puncturedSourceDisk (a : ℂ) (r : ℝ) : IsOpen (puncturedSourceDisk a r) :=
  isOpen_ne.inter (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

def puncturedSourceDiskHomeomorph (a : ℂ) (r : ℝ) (hr : 0 < r) :
    PuncturedUnitDisk ≃ₜ puncturedSourceDisk a r := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  refine
    { toFun := fun z => ⟨a + (r : ℂ) * z.val, ?_, ?_⟩
      invFun := fun z => ⟨(z.val - a) / (r : ℂ),
        div_ne_zero (sub_ne_zero.mpr z.property.1) hr0, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  · intro h
    apply mul_ne_zero hr0 z.property.1
    linear_combination h
  · simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left z.property.2 hr
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact (div_lt_one hr).mpr z.property.2
  · intro z
    apply Subtype.ext
    dsimp
    field_simp
    ring
  · intro z
    apply Subtype.ext
    dsimp
    field_simp
    ring

theorem isPathConnected_puncturedSourceDisk (a : ℂ) (r : ℝ) (hr : 0 < r) :
    IsPathConnected (puncturedSourceDisk a r) :=
  isPathConnected_iff_pathConnectedSpace.mpr
    ((puncturedSourceDiskHomeomorph a r hr).surjective.pathConnectedSpace
      (puncturedSourceDiskHomeomorph a r hr).continuous)

/-- Every punctured neighborhood contains a connected punctured source disk. -/
theorem exists_puncturedSourceDisk_subset {a : ℂ} {S : Set ℂ} (hS : S ∈ 𝓝[≠] a) :
    ∃ r : ℝ, 0 < r ∧ puncturedSourceDisk a r ⊆ S := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hS
  refine ⟨r, hr, fun z hz => hsub ?_⟩
  exact ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hz.2, hz.1⟩

end
end GaloisForLFunctions.HTGeometry
