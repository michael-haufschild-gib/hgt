import GaloisForLFunctions.RHTower.XiMarkedImageCover
import GaloisForLFunctions.HTGeometry.PuncturedDiskCover

/-!
# Explicit peripheral charts for the actual marked Xi target

The radius-one-quarter disks around zero and minus one are disjoint. Affine
normalization identifies each punctured target neighborhood with the punctured
unit disk, with exact projection and inverse formulas.
-/

open Topology Set Function

namespace RHTower.XiMarkedMonodromy
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two marked values, indexed without any additional parameters. -/
def peripheralCenter (b : Bool) : ℂ := if b then -1 else 0

/-- Disjoint radius-one-quarter neighborhoods in the marked target. -/
def peripheralTarget (b : Bool) : Set Target :=
  {z | ‖z.val - peripheralCenter b‖ < 1 / 4}

theorem isOpen_peripheralTarget (b : Bool) : IsOpen (peripheralTarget b) :=
  isOpen_lt (continuous_subtype_val.sub continuous_const).norm continuous_const

theorem target_ne_peripheralCenter (b : Bool) (z : Target) : z.val ≠ peripheralCenter b := by
  cases b
  · exact z.property.1
  · exact z.property.2

private theorem norm_quarter_lt (z : PuncturedUnitDisk) : ‖z.val / (4 : ℂ)‖ < 1 / 4 := by
  rw [norm_div]
  norm_num
  linarith [z.property.2]

/-- The inverse affine chart lands in the actual twice-punctured target. -/
def peripheralPoint (b : Bool) (z : PuncturedUnitDisk) : Target := by
  have hz0 : z.val / (4 : ℂ) ≠ 0 := div_ne_zero z.property.1 (by norm_num)
  have hnorm : ‖z.val / (4 : ℂ)‖ < 1 := lt_trans (norm_quarter_lt z) (by norm_num)
  refine ⟨peripheralCenter b + z.val / 4, ?_, ?_⟩
  · cases b
    · simpa [peripheralCenter] using hz0
    · intro h
      have he : z.val / (4 : ℂ) = 1 := by
        change -1 + z.val / 4 = 0 at h
        linear_combination h
      rw [he, norm_one] at hnorm
      exact (lt_irrefl 1) hnorm
  · cases b
    · intro h
      have he : z.val / (4 : ℂ) = -1 := by simpa [peripheralCenter] using h
      rw [he, norm_neg, norm_one] at hnorm
      exact (lt_irrefl 1) hnorm
    · intro h
      apply hz0
      change -1 + z.val / 4 = -1 at h
      linear_combination h

@[simp] theorem peripheralPoint_val (b : Bool) (z : PuncturedUnitDisk) :
    (peripheralPoint b z : ℂ) = peripheralCenter b + z.val / 4 := rfl

theorem peripheralPoint_mem (b : Bool) (z : PuncturedUnitDisk) :
    peripheralPoint b z ∈ peripheralTarget b := by
  change ‖peripheralCenter b + z.val / 4 - peripheralCenter b‖ < 1 / 4
  simpa only [add_sub_cancel_left] using norm_quarter_lt z

/-- Exact normalized punctured chart at each actual marked value. -/
def peripheralTargetChart (b : Bool) : peripheralTarget b ≃ₜ PuncturedUnitDisk where
  toFun z := ⟨(z.val.val - peripheralCenter b) * 4,
    mul_ne_zero (sub_ne_zero.mpr (target_ne_peripheralCenter b z.val)) (by norm_num), by
      rw [norm_mul]
      norm_num
      have h := z.property
      change ‖z.val.val - peripheralCenter b‖ < 1 / 4 at h
      linarith⟩
  invFun z := ⟨peripheralPoint b z, peripheralPoint_mem b z⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    change peripheralCenter b + (z.val.val - peripheralCenter b) * 4 / 4 = z.val.val
    ring
  right_inv z := by
    apply Subtype.ext
    change (peripheralCenter b + z.val / 4 - peripheralCenter b) * 4 = z.val
    ring
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_const.add (continuous_subtype_val.div_const _)

@[simp] theorem peripheralTargetChart_val (b : Bool) (z : peripheralTarget b) :
    (peripheralTargetChart b z : ℂ) = (z.val.val - peripheralCenter b) * 4 := rfl

@[simp] theorem peripheralTargetChart_symm_val (b : Bool) (z : PuncturedUnitDisk) :
    ((peripheralTargetChart b).symm z).val.val = peripheralCenter b + z.val / 4 := rfl

theorem peripheralTargetChart_projection (b : Bool) (z : peripheralTarget b) :
    z.val.val = peripheralCenter b + (peripheralTargetChart b z : ℂ) / 4 := by
  rw [peripheralTargetChart_val]
  ring

theorem disjoint_peripheralTarget : Pairwise (Disjoint on peripheralTarget) := by
  have h : Disjoint (peripheralTarget false) (peripheralTarget true) := by
    rw [disjoint_left]
    intro z h0 h1
    change ‖z.val - peripheralCenter false‖ < 1 / 4 at h0
    change ‖z.val - peripheralCenter true‖ < 1 / 4 at h1
    simp only [peripheralCenter, Bool.false_eq_true, ↓reduceIte, sub_zero] at h0
    simp only [peripheralCenter, ↓reduceIte, sub_neg_eq_add] at h1
    have hn := norm_sub_le (z.val + 1) z.val
    simp only [add_sub_cancel_left, norm_one] at hn
    linarith
  intro i j hij
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact h
  · exact h.symm
  · exact (hij rfl).elim

end
end RHTower.XiMarkedMonodromy
