import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite Gram approximation detects a unit vector

A Gram matrix close to the identity controls synthesis coefficients uniformly.
A unit vector within distance one half of that synthesis space must therefore
have a fixed positive squared coordinate mass against the spanning family.
-/

noncomputable section

open Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Entrywise Gram error bounds the error of every finite quadratic form. -/
theorem abs_norm_sum_smul_sq_sub_sum_sq_le
    (v : I → E) (a : I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgram : ∀ i j, |⟪v i, v j⟫ - if i = j then 1 else 0| ≤ δ) :
    |‖∑ i, a i • v i‖ ^ 2 - ∑ i, a i ^ 2| ≤
      (Fintype.card I : ℝ) * δ * ∑ i, a i ^ 2 := by
  have hnorm : ‖∑ i, a i • v i‖ ^ 2 =
      ∑ i, ∑ j, a i * a j * ⟪v i, v j⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    calc
      _ = a i * a j * ⟪v j, v i⟫ := by ring
      _ = _ := by rw [real_inner_comm (v j) (v i)]
  have hdiag : (∑ i, ∑ j, a i * a j * (if i = j then (1 : ℝ) else 0)) =
      ∑ i, a i ^ 2 := by
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true, sq]
  have hdiff : ‖∑ i, a i • v i‖ ^ 2 - ∑ i, a i ^ 2 =
      ∑ i, ∑ j, a i * a j * (⟪v i, v j⟫ - if i = j then 1 else 0) := by
    rw [hnorm, ← hdiag, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
  rw [hdiff]
  calc
    _ ≤ ∑ i, ∑ j, |a i| * |a j| * δ := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hgram i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i, |a i|) ^ 2 * δ := by
      rw [sq, sum_mul_sum, sum_mul]
      exact sum_congr rfl fun i _ => by rw [sum_mul]
    _ ≤ ((Fintype.card I : ℝ) * ∑ i, a i ^ 2) * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ
      simpa only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul,
        mul_one, sq_abs] using
        (sum_mul_sq_le_sq_mul_sq (univ : Finset I) (fun _ => (1 : ℝ)) (fun i => |a i|))
    _ = _ := by ring

/-- A fixed entrywise neighborhood of the identity gives a uniform lower Gram bound. -/
theorem half_sum_sq_le_norm_sum_smul_sq
    (v : I → E)
    (hgram : ∀ i j, |⟪v i, v j⟫ - if i = j then 1 else 0| ≤
      1 / (2 * ((Fintype.card I : ℝ) + 1))) (a : I → ℝ) :
    (∑ i, a i ^ 2) / 2 ≤ ‖∑ i, a i • v i‖ ^ 2 := by
  have hc : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hδ : (0 : ℝ) ≤ 1 / (2 * ((Fintype.card I : ℝ) + 1)) := by positivity
  have h := abs_norm_sum_smul_sq_sub_sum_sq_le v a hδ hgram
  have hcoef : (Fintype.card I : ℝ) *
      (1 / (2 * ((Fintype.card I : ℝ) + 1))) ≤ 1 / 2 := by
    have h' : (Fintype.card I : ℝ) / (2 * ((Fintype.card I : ℝ) + 1)) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only
    convert h' using 1
    ring
  have hs := mul_le_mul_of_nonneg_right hcoef
    (sum_nonneg (s := univ) fun i _ => sq_nonneg (a i))
  have hlo := (abs_le.mp h).1
  linarith only [hs, hlo]

/-- Uniform finite-span approximation supplies positive coordinate mass.
The numerical constant merely records the elementary Cauchy--Schwarz estimate. -/
theorem coordinate_mass_ge_of_finite_approximation
    (v : I → E)
    (hgram : ∀ i j, |⟪v i, v j⟫ - if i = j then 1 else 0| ≤
      1 / (2 * ((Fintype.card I : ℝ) + 1)))
    (x : E) (hx : ‖x‖ = 1) (a : I → ℝ)
    (happrox : ‖x - ∑ i, a i • v i‖ ^ 2 ≤ 1 / 4) :
    1 / 18 ≤ ∑ i, ⟪x, v i⟫ ^ 2 := by
  let z : E := ∑ i, a i • v i
  have hdist : ‖x - z‖ ≤ 1 / 2 := by
    change ‖x - z‖ ^ 2 ≤ 1 / 4 at happrox
    nlinarith only [happrox, norm_nonneg (x - z)]
  have hznorm : ‖z‖ ≤ 3 / 2 := by
    have ht := norm_add_le (z - x) x
    rw [sub_add_cancel, norm_sub_rev, hx] at ht
    linarith only [ht, hdist]
  have hac : (∑ i, a i ^ 2) ≤ 9 / 2 := by
    have h := half_sum_sq_le_norm_sum_smul_sq v hgram a
    change (∑ i, a i ^ 2) / 2 ≤ ‖z‖ ^ 2 at h
    nlinarith only [h, hznorm, norm_nonneg z]
  have hic : |⟪x, x - z⟫| ≤ ‖x‖ * ‖x - z‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x (x - z)
  have hinner : 1 / 2 ≤ ⟪x, z⟫ := by
    rw [hx, one_mul, inner_sub_right, real_inner_self_eq_norm_sq, hx] at hic
    have h := (le_abs_self (1 ^ 2 - ⟪x, z⟫)).trans hic
    nlinarith only [h, hdist]
  have hcs : ⟪x, z⟫ ^ 2 ≤ (∑ i, a i ^ 2) * ∑ i, ⟪x, v i⟫ ^ 2 := by
    have heq : ⟪x, z⟫ = ∑ i, a i * ⟪x, v i⟫ := by
      simp only [z, inner_sum, real_inner_smul_right]
    rw [heq]
    exact sum_mul_sq_le_sq_mul_sq univ a (fun i => ⟪x, v i⟫)
  have hupper := mul_le_mul_of_nonneg_right hac
    (sum_nonneg (s := univ) fun i _ => sq_nonneg ⟪x, v i⟫)
  nlinarith only [hinner, hcs, hupper]

end GaloisForLFunctions.HTGeometry
