import GaloisForLFunctions.BiScaleUncertainty.EvenPrimePairMomentCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact three-prime scalar sixth-moment collision

Centered residue rows at three, five and seven give a symbolic sixth-moment
collision when two cubic contributions cancel. Explicit positive real cube
roots satisfy the cancellation. No complete residue period is enumerated.
-/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
set_option autoImplicit false

private theorem sum_sixth_flip_zero {α β : Type*} [Fintype α] [Fintype β]
    (X : α → ℝ) (W : β → ℝ) (hX : ∑ x, X x = 0)
    (hW : ∑ y, W y = 0) (hW3 : ∑ y, (W y)^3 = 0) :
    (∑ x, ∑ y, ((X x+W y)^6-(X x-W y)^6)) = 0 := by
  have hp (x y : ℝ) : (x+y)^6-(x-y)^6 = 12*x^5*y+40*x^3*y^3+12*x*y^5 := by ring
  have hi (x : α) : (∑ y, ((X x+W y)^6-(X x-W y)^6)) = 12*X x * ∑ y, (W y)^5 := by
    simp_rw [hp,Finset.sum_add_distrib,← Finset.mul_sum,hW,hW3,mul_zero,zero_add]
  simp_rw [hi]
  rw [← Finset.sum_mul,← Finset.mul_sum,hX]
  ring

private theorem two_row_cube_sum (u v : ℝ) :
    (∑ y : ZMod 5, ∑ z : ZMod 7, (u*residueRow 5 y-v*residueRow 7 z)^3) =
      420*u^3-1050*v^3 := by
  have h5 : (∑ y : ZMod 5, residueRow 5 y) = 0 := by
    simpa using sum_residueRow_shift 5 (0 : ZMod 5)
  have h7 : (∑ z : ZMod 7, residueRow 7 z) = 0 := by
    simpa using sum_residueRow_shift 7 (0 : ZMod 7)
  have h53 : (∑ y : ZMod 5, (residueRow 5 y)^3) = 60 := by
    rw [sum_residueRow_pow]; norm_num
  have h73 : (∑ z : ZMod 7, (residueRow 7 z)^3) = 210 := by
    rw [sum_residueRow_pow]; norm_num
  have hp (x y : ℝ) : (u*x-v*y)^3 =
      u^3*x^3 - (3*u^2*v*x^2)*y + (3*u*v^2*x)*y^2 - v^3*y^3 := by ring
  simp only [hp,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum]
  simp only [h7,h73,mul_zero,sub_zero,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
  have ht : (∑ y : ZMod 5, 3*u*v^2*residueRow 5 y * ∑ z : ZMod 7, residueRow 7 z^2) = 0 := by
    rw [← Finset.sum_mul,← Finset.mul_sum,h5]
    ring
  rw [ht]
  simp only [add_zero]
  rw [← Finset.mul_sum,h53]
  ring

/-- The exact three-row sixth moment loses a simultaneous sign flip at the cubic cancellation. -/
theorem three_prime_sixth_collision (u v : ℝ) (hu : u^3 = 5) (hv : v^3 = 2) :
    (∑ x : ZMod 3, ∑ y : ZMod 5, ∑ z : ZMod 7,
      (residueRow 3 x+u*residueRow 5 y-v*residueRow 7 z)^6) =
    ∑ x : ZMod 3, ∑ y : ZMod 5, ∑ z : ZMod 7,
      (residueRow 3 x-u*residueRow 5 y+v*residueRow 7 z)^6 := by
  let W : ZMod 5 × ZMod 7 → ℝ := fun y => u*residueRow 5 y.1-v*residueRow 7 y.2
  have hX : (∑ x : ZMod 3, residueRow 3 x) = 0 := by
    simpa using sum_residueRow_shift 3 (0 : ZMod 3)
  have hW : (∑ y, W y) = 0 := by
    rw [Fintype.sum_prod_type]
    simp only [W,Finset.sum_sub_distrib,← Finset.mul_sum]
    have h5 : (∑ y : ZMod 5, residueRow 5 y) = 0 := by
      simpa using sum_residueRow_shift 5 (0 : ZMod 5)
    have h7 : (∑ z : ZMod 7, residueRow 7 z) = 0 := by
      simpa using sum_residueRow_shift 7 (0 : ZMod 7)
    simp only [h7,mul_zero,sub_zero,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
    rw [← Finset.mul_sum,h5]
    ring
  have hW3 : (∑ y, (W y)^3) = 0 := by
    rw [Fintype.sum_prod_type]
    change (∑ y : ZMod 5, ∑ z : ZMod 7, (u*residueRow 5 y-v*residueRow 7 z)^3) = 0
    rw [two_row_cube_sum,hu,hv]
    norm_num
  have hh := sum_sixth_flip_zero (residueRow 3) W hX hW hW3
  simp only [Fintype.sum_prod_type,W] at hh
  have hp (x y z : ℝ) : x+(u*y-v*z) = x+u*y-v*z := by ring
  have hm (x y z : ℝ) : x-(u*y-v*z) = x-u*y+v*z := by ring
  simp_rw [hp,hm,Finset.sum_sub_distrib] at hh
  exact sub_eq_zero.mp hh

/-- Positive cubic roots used by the actual counterexample are explicit real constants. -/
theorem positive_cubic_cancellation_constants :
    0 < (5 : ℝ)^(3 : ℝ)⁻¹ ∧ 0 < (2 : ℝ)^(3 : ℝ)⁻¹ ∧
      ((5 : ℝ)^(3 : ℝ)⁻¹)^3 = 5 ∧ ((2 : ℝ)^(3 : ℝ)⁻¹)^3 = 2 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _,Real.rpow_pos_of_pos (by norm_num) _,?_,?_⟩
  · exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
  · exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
