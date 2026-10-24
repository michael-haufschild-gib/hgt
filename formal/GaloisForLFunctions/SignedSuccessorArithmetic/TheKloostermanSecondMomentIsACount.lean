import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Complex.Basic

/-!
# The Kloosterman second moment is a count

The balanced cross-scale Gram of Bézout–Valuation Incidence reduces to bilinear forms in the
Kloosterman fractions `k q̄ / p`, so the finite-field model of the successor input at balanced
scales is the Kloosterman sum `K(a, b) = Σ_{x ≠ 0} ψ(a x + b x⁻¹)`: it couples the additive
structure (the character `ψ`) with the multiplicative inverse. Its pointwise size `≤ 2√q` is
Weil's theorem; its mean square is a count:

  `Σ_{a ∈ F} |K(a, b)|² = q (q − 1)`  (`sum_normSq_kloosterman`),

because orthogonality in `a` keeps only the diagonal `x = y`. With `K(0, b) = −1` for `b ≠ 0`
(`kloosterman_zero_left`), the mean square over `a ≠ 0` is `q − 1/(q − 1)`
(`sum_normSq_kloosterman_ne_zero`): square-root cancellation on average, as an exact identity.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset AddChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Kloosterman sum `K(a, b) = Σ_{x ≠ 0} ψ(a x + b x⁻¹)`. -/
def kloosterman (ψ : AddChar F ℂ) (a b : F) : ℂ :=
  ∑ x ∈ univ.filter (· ≠ (0 : F)), ψ (a * x + b * x⁻¹)

theorem card_units_filter : (univ.filter (· ≠ (0 : F))).card = Fintype.card F - 1 := by
  rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ]

omit [DecidableEq F] in
/-- Complex conjugation inverts an additive character of a finite field. -/
theorem conj_addChar (ψ : AddChar F ℂ) (t : F) : (starRingEnd ℂ) (ψ t) = ψ (-t) := by
  have hR : 0 < ringChar F := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite F)
  rw [starComp_apply hR, inv_apply]

/-- **The Kloosterman second moment is a count.** `Σ_a |K(a, b)|² = q (q − 1)`. -/
theorem sum_normSq_kloosterman {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (b : F) :
    ∑ a : F, Complex.normSq (kloosterman ψ a b) = Fintype.card F * (Fintype.card F - 1) := by
  have hterm : ∀ x y : F, ∑ a : F, ψ (a * x + b * x⁻¹) * ψ (-(a * y + b * y⁻¹)) =
      if x = y then (Fintype.card F : ℂ) else 0 := by
    intro x y
    have hsplit : ∀ a : F, ψ (a * x + b * x⁻¹) * ψ (-(a * y + b * y⁻¹)) =
        ψ (a * (x - y)) * ψ (b * x⁻¹ - b * y⁻¹) := fun a => by
      rw [← map_add_eq_mul, ← map_add_eq_mul]; congr 1; ring
    simp_rw [hsplit, ← sum_mul, sum_mulShift _ hψ, sub_eq_zero]
    split_ifs with h
    · rw [h, sub_self, map_zero_eq_one, mul_one]
    · simp
  have hcomplex : ∑ a : F, kloosterman ψ a b * (starRingEnd ℂ) (kloosterman ψ a b) =
      (Fintype.card F : ℂ) * (univ.filter (· ≠ (0 : F))).card := by
    simp only [kloosterman, map_sum, conj_addChar, sum_mul_sum]
    rw [sum_comm, sum_congr rfl fun x _ => sum_comm.trans (sum_congr rfl fun y _ => hterm x y)]
    rw [sum_congr rfl fun x hx => (sum_ite_eq (univ.filter (· ≠ (0 : F))) x
      fun _ => (Fintype.card F : ℂ)).trans (if_pos hx), sum_const, nsmul_eq_mul, mul_comm]
  have hreal : ∑ a : F, ((Complex.normSq (kloosterman ψ a b) : ℝ) : ℂ) =
      (Fintype.card F : ℂ) * (univ.filter (· ≠ (0 : F))).card := by
    rw [← hcomplex]
    exact sum_congr rfl fun a _ => (Complex.mul_conj _).symm
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [card_units_filter, Nat.cast_sub hq, Nat.cast_one] at hreal
  apply Complex.ofReal_injective
  push_cast
  exact hreal

/-- At `a = 0` the Kloosterman sum is a complete character sum minus one: `K(0, b) = −1`. -/
theorem kloosterman_zero_left {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F} (hb : b ≠ 0) :
    kloosterman ψ 0 b = -1 := by
  have hfull := sum_mulShift (ψ := ψ) b hψ
  rw [if_neg hb] at hfull
  have hsplit : ∑ x : F, ψ (x * b) = ψ (0 * b) + ∑ x ∈ univ.filter (· ≠ (0 : F)), ψ (x * b) := by
    rw [← sum_filter_add_sum_filter_not univ (· = (0 : F)), filter_eq' univ (0 : F),
      if_pos (mem_univ _), sum_singleton]
  have hinv : ∑ x ∈ univ.filter (· ≠ (0 : F)), ψ (b * x⁻¹) =
      ∑ x ∈ univ.filter (· ≠ (0 : F)), ψ (x * b) := by
    refine sum_nbij' (fun x => x⁻¹) (fun x => x⁻¹) (by simp) (by simp) (by simp) (by simp)
      fun x _ => by rw [mul_comm]
  rw [kloosterman]
  simp only [zero_mul, zero_add]
  rw [hinv]
  rw [zero_mul, map_zero_eq_one] at hsplit
  simp only [ne_eq] at hsplit ⊢
  linear_combination hsplit.symm.trans hfull

/-- Over `a ≠ 0`: `Σ_{a ≠ 0} |K(a, b)|² = q² − q − 1`. -/
theorem sum_normSq_kloosterman_ne_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {b : F}
    (hb : b ≠ 0) :
    ∑ a ∈ univ.filter (· ≠ (0 : F)), Complex.normSq (kloosterman ψ a b) =
      (Fintype.card F : ℝ) ^ 2 - Fintype.card F - 1 := by
  have h := sum_normSq_kloosterman hψ b
  rw [← sum_filter_add_sum_filter_not univ (· ≠ (0 : F))] at h
  have hz : univ.filter (fun a : F => ¬ a ≠ 0) = {0} := by ext; simp
  rw [hz, sum_singleton, kloosterman_zero_left hψ hb] at h
  simp only [map_one, Complex.normSq_neg] at h
  nlinarith [h]

end GaloisForLFunctions.SignedSuccessorArithmetic
