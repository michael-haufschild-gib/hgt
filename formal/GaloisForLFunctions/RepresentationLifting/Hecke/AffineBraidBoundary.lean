import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# Exact braid boundary for affine Hecke deformations

An affine deformation of each involution satisfies the quadratic Hecke
relation. Its braid defect reduces to `a²b(R-S)` for an involutive braid
pair. On the three-letter permutation representation, braid compatibility
survives exactly at `q² = 1` or `q² = -1`: the original swaps or the scalar
sign action. Thus the two-sector specialization mechanism of
Kim--Lee--Oh, arXiv:2611.20790, does not extend by this affine formula alone.
-/

namespace GaloisForLFunctions.RepresentationLifting.Hecke
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A common affine deformation of an endomorphism. -/
def affineGenerator (R : Module.End ℂ V) (a b : ℂ) : Module.End ℂ V := a • 1 + b • R

theorem affine_braid_defect (R S : Module.End ℂ V) (a b : ℂ) :
    affineGenerator R a b * affineGenerator S a b * affineGenerator R a b -
      affineGenerator S a b * affineGenerator R a b * affineGenerator S a b =
    (a ^ 2 * b) • (R - S) + (a * b ^ 2) • (R * R - S * S) +
      b ^ 3 • (R * S * R - S * R * S) := by
  simp only [affineGenerator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, smul_sub, mul_assoc]
  module

theorem affine_braid_iff (R S : Module.End ℂ V)
    (hR : R * R = 1) (hS : S * S = 1) (hbraid : R * S * R = S * R * S)
    (a b : ℂ) :
    affineGenerator R a b * affineGenerator S a b * affineGenerator R a b =
      affineGenerator S a b * affineGenerator R a b * affineGenerator S a b ↔
        a = 0 ∨ b = 0 ∨ R = S := by
  rw [← sub_eq_zero, affine_braid_defect, hR, hS, hbraid]
  simp only [sub_self, smul_zero, add_zero, smul_eq_zero, mul_eq_zero,
    sq_eq_zero_iff, sub_eq_zero]
  tauto

abbrev Triple := ℂ × ℂ × ℂ

def swapLeft : Module.End ℂ Triple where
  toFun v := (v.2.1, v.1, v.2.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def swapRight : Module.End ℂ Triple where
  toFun v := (v.1, v.2.2, v.2.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem swapLeft_sq : swapLeft * swapLeft = 1 := by ext <;> rfl
theorem swapRight_sq : swapRight * swapRight = 1 := by ext <;> rfl
theorem swaps_braid : swapLeft * swapRight * swapLeft = swapRight * swapLeft * swapRight := by
  ext <;> rfl

theorem swaps_ne : swapLeft ≠ swapRight := by
  intro h
  have hh := congrArg (fun U : Module.End ℂ Triple => (U (1, 0, 0)).1) h
  change (0 : ℂ) = 1 at hh
  exact zero_ne_one hh

/-- Exact surviving parameters of the affine deformation of the three-letter permutation action. -/
theorem permutation_hecke_braid_iff (q : ℂ) :
    affineGenerator swapLeft ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) *
        affineGenerator swapRight ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) *
        affineGenerator swapLeft ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) =
      affineGenerator swapRight ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) *
        affineGenerator swapLeft ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) *
        affineGenerator swapRight ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) ↔
      q ^ 2 = 1 ∨ q ^ 2 = -1 := by
  rw [affine_braid_iff swapLeft swapRight swapLeft_sq swapRight_sq swaps_braid]
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  simp only [swaps_ne, or_false, div_eq_zero_iff, htwo, sub_eq_zero,
    add_eq_zero_iff_eq_neg]

/-- Every deformed involution satisfies the quadratic Hecke relation, even when braid compatibility fails. -/
theorem affine_hecke_quadratic (R : Module.End ℂ V) (hR : R * R = 1) (q : ℂ) :
    affineGenerator R ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) *
        affineGenerator R ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) =
      (q ^ 2 - 1) • affineGenerator R ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) +
        q ^ 2 • 1 := by
  simp only [affineGenerator, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, hR]
  module

/-- The noncollapsed surviving branch is the original permutation action. -/
theorem affine_hecke_at_square_one (R : Module.End ℂ V) {q : ℂ} (hq : q ^ 2 = 1) :
    affineGenerator R ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) = R := by
  norm_num [affineGenerator, hq]

/-- The other surviving branch collapses every generator to minus the identity. -/
theorem affine_hecke_at_square_neg_one (R : Module.End ℂ V) {q : ℂ} (hq : q ^ 2 = -1) :
    affineGenerator R ((q ^ 2 - 1) / 2) ((q ^ 2 + 1) / 2) = -1 := by
  norm_num [affineGenerator, hq]

#print axioms affine_hecke_quadratic

#print axioms affine_braid_defect
#print axioms permutation_hecke_braid_iff
end
end GaloisForLFunctions.RepresentationLifting.Hecke
