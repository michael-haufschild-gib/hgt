import GaloisForLFunctions.RHTower.QuasiRHShiftCorrelation
import Mathlib.Tactic.FieldSimp

/-!
# Complete-field character correlations

Fractional-linear substitution gives the translation Gram kernel `qδ-1`.
Its exact convolution identity retains the negative square of the coefficient
sum. Applied to the three-point character family, it gives a complete-parameter
mean-square bound without a pointwise character-sum estimate.
-/

noncomputable section

namespace RHTower.QuasiRHShiftCorrelation

open Finset
open scoped Classical

variable {K : Type*} [Field K]

/-- A fractional-linear permutation with its pole exchanged with its omitted value. -/
def fractionalShiftEquiv (A B d : K) (hB : B ≠ 0) : K ≃ K where
  toFun x := A + B / (x - d)
  invFun t := d + B / (t - A)
  left_inv x := by dsimp; rw [add_sub_cancel_left, div_div_cancel₀ hB]; ring
  right_inv t := by dsimp; rw [add_sub_cancel_left, div_div_cancel₀ hB]; ring

section Finite

variable [Fintype K]

theorem character_div (χ : MulChar K ℂ) (x y : K) :
    χ (x / y) = χ x * star (χ y) := by
  rw [div_eq_mul_inv, map_mul, MulChar.star_apply', MulChar.inv_apply']

private theorem character_mul_star (χ : MulChar K ℂ) (x : K) :
    χ x * star (χ x) = if x = 0 then 0 else 1 := by
  classical
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · rw [if_neg hx, MulChar.star_apply', MulChar.inv_apply_eq_inv']
    exact mul_inv_cancel₀ (MulChar.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hx))

private theorem mul_star_norm_sq (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' z

theorem character_norm_sq (χ : MulChar K ℂ) (x : K) :
    ‖χ x‖ ^ 2 = if x = 0 then 0 else 1 := by
  classical
  have h := character_mul_star χ x
  rw [mul_star_norm_sq] at h
  by_cases hx : x = 0
  · simp [hx, MulChar.map_zero]
  · rw [if_neg hx]
    apply Complex.ofReal_injective
    rw [if_neg hx] at h
    exact h

/-- The complete translation Gram kernel of a nonprincipal character. -/
theorem character_translation_gram (χ : MulChar K ℂ) (hχ : χ ≠ 1) (u v : K) :
    ∑ x : K, star (χ (u - x)) * χ (v - x) =
      (if u = v then (Fintype.card K : ℂ) else 0) - 1 := by
  classical
  by_cases huv : u = v
  · subst v
    have hp (x : K) : star (χ (u - x)) * χ (u - x) =
        1 - if x = u then 1 else 0 := by
      rw [mul_comm, character_mul_star]
      by_cases hxu : x = u
      · simp [hxu]
      · simp [hxu, sub_eq_zero, Ne.symm hxu]
    simp_rw [hp]
    simp
  · rw [if_neg huv, zero_sub]
    let e := fractionalShiftEquiv 1 (u - v) u (sub_ne_zero.mpr huv)
    have hp (x : K) :
        star (χ (u - x)) * χ (v - x) + (if x = u then 1 else 0) = χ (e x) := by
      by_cases hxu : x = u
      · subst x
        simp [e, fractionalShiftEquiv, MulChar.map_zero]
      · rw [if_neg hxu, add_zero, mul_comm, ← character_div]
        apply congrArg χ
        change (v - x) / (u - x) = 1 + (u - v) / (x - u)
        field_simp [sub_ne_zero.mpr hxu, sub_ne_zero.mpr (Ne.symm hxu)]
        ring
    have hs := sum_congr (s₁ := (univ : Finset K)) rfl (fun x _ => hp x)
    rw [sum_add_distrib, e.sum_comp, MulChar.sum_eq_zero_of_ne_one hχ] at hs
    simp only [sum_ite_eq', mem_univ, if_true] at hs
    exact eq_neg_of_add_eq_zero_left hs

/-- Convolution with the conjugate translates of a multiplicative character. -/
def characterConvolution (χ : MulChar K ℂ) (a : K → ℂ) (x : K) : ℂ :=
  ∑ t : K, a t * star (χ (t - x))

/-- Exact complete-field energy, with the constant component subtracted. -/
theorem characterConvolution_energy (χ : MulChar K ℂ) (hχ : χ ≠ 1) (a : K → ℂ) :
    ∑ x : K, ‖characterConvolution χ a x‖ ^ 2 =
      (Fintype.card K : ℝ) * ∑ t : K, ‖a t‖ ^ 2 - ‖∑ t : K, a t‖ ^ 2 := by
  classical
  have hp (x : K) :
      characterConvolution χ a x * star (characterConvolution χ a x) =
        ∑ u : K, ∑ v : K, a u * star (a v) * (star (χ (u - x)) * χ (v - x)) := by
    simp only [characterConvolution, star_sum, star_mul, star_star, sum_mul_sum]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    ring
  have he :
      ∑ x : K, characterConvolution χ a x * star (characterConvolution χ a x) =
        (Fintype.card K : ℂ) * ∑ u : K, a u * star (a u) -
          (∑ u : K, a u) * star (∑ v : K, a v) := by
    simp_rw [hp]
    rw [sum_comm]
    have hs (u : K) :
        (∑ x : K, ∑ v : K, a u * star (a v) * (star (χ (u - x)) * χ (v - x))) =
          ∑ v : K, a u * star (a v) *
            ((if u = v then (Fintype.card K : ℂ) else 0) - 1) := by
      rw [sum_comm]
      simp_rw [← mul_sum, character_translation_gram χ hχ]
    simp_rw [hs, mul_sub, mul_ite, mul_zero, mul_one, sum_sub_distrib,
      sum_ite_eq, mem_univ, if_true]
    rw [← sum_mul, ← sum_mul_sum, ← star_sum]
    ring
  simp_rw [mul_star_norm_sq] at he
  exact_mod_cast he

/-- Three-point family obtained by normalizing four shifts by a cross ratio. -/
def threePointCharacterSum (χ : MulChar K ℂ) (t : K) : ℂ :=
  ∑ x : K, χ (x * (x - 1) / (x - t))

theorem threePointCharacterSum_eq_convolution (χ : MulChar K ℂ) (t : K) :
    threePointCharacterSum χ t = characterConvolution χ (fun x => χ (x * (x - 1))) t := by
  simp only [threePointCharacterSum, characterConvolution, character_div]

private theorem quadratic_argument_energy (χ : MulChar K ℂ) :
    ∑ x : K, ‖χ (x * (x - 1))‖ ^ 2 = (Fintype.card K : ℝ) - 2 := by
  classical
  have hp (x : K) : ‖χ (x * (x - 1))‖ ^ 2 =
      1 - (if x = 0 then 1 else 0) - (if x = 1 then 1 else 0) := by
    rw [character_norm_sq]
    by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;>
      simp_all [mul_eq_zero, sub_eq_zero]
  simp_rw [hp, sum_sub_distrib]
  simp
  ring

/-- The exact second moment keeps the Jacobi-sum correction. -/
theorem threePointCharacterSum_energy (χ : MulChar K ℂ) (hχ : χ ≠ 1) :
    ∑ t : K, ‖threePointCharacterSum χ t‖ ^ 2 =
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 2) -
        ‖∑ x : K, χ (x * (x - 1))‖ ^ 2 := by
  simp_rw [threePointCharacterSum_eq_convolution]
  rw [characterConvolution_energy χ hχ, quadratic_argument_energy]

theorem threePointCharacterSum_energy_le (χ : MulChar K ℂ) (hχ : χ ≠ 1) :
    ∑ t : K, ‖threePointCharacterSum χ t‖ ^ 2 ≤
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 2) := by
  rw [threePointCharacterSum_energy χ hχ]
  exact sub_le_self _ (sq_nonneg _)

/-- Complete four-shift correlation, with zero denominators contributing zero. -/
def fourShiftCharacterSum (χ : MulChar K ℂ) (a b c d : K) : ℂ :=
  ∑ x : K, χ ((x - a) * (x - b) / ((x - c) * (x - d)))

theorem fourShiftCharacterSum_eq_polynomial (χ : MulChar K ℂ) (hχ : χ ^ 6 = 1)
    (a b c d : K) :
    fourShiftCharacterSum χ a b c d =
      ∑ x : K, χ ((sexticCorrelationPolynomial a b c d).eval x) := by
  simp only [fourShiftCharacterSum, character_div, map_mul,
    sexticCorrelationPolynomial_character χ hχ]

/-- Cross-ratio normalization retains the missing point at infinity as `+1`. -/
theorem fourShiftCharacterSum_crossRatio (χ : MulChar K ℂ) (a b c d : K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d) :
    fourShiftCharacterSum χ a b c d + 1 =
      χ ((b - a) / (c - d)) *
        threePointCharacterSum χ ((b - d) * (c - a) / ((b - a) * (c - d))) := by
  let A := (b - d) / (b - a)
  let B := A * (d - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hda : d - a ≠ 0 := sub_ne_zero.mpr (Ne.symm had)
  have hbd' : b - d ≠ 0 := sub_ne_zero.mpr hbd
  have hcd' : c - d ≠ 0 := sub_ne_zero.mpr hcd
  have hB : B ≠ 0 := mul_ne_zero (div_ne_zero hbd' hba) hda
  let e := fractionalShiftEquiv A B d hB
  have hparam : e c = (b - d) * (c - a) / ((b - a) * (c - d)) := by
    change A + B / (c - d) = _
    dsimp [A, B]
    field_simp [hba, hcd']
    ring
  have hp (x : K) :
      χ ((x - a) * (x - b) / ((x - c) * (x - d))) +
        (if x = d then 1 else 0) =
          χ ((b - a) / (c - d)) * χ (e x * (e x - 1) / (e x - e c)) := by
    by_cases hxd : x = d
    · subst x
      simp only [sub_self, mul_zero, div_zero, MulChar.map_zero, zero_add]
      rw [← map_mul]
      have he : e d - e c ≠ 0 := sub_ne_zero.mpr (fun h => hcd (e.injective h).symm)
      have hr : (b - a) / (c - d) * (e d * (e d - 1) / (e d - e c)) = 1 := by
        rw [← mul_div_assoc, div_eq_iff he]
        dsimp [e, fractionalShiftEquiv, A, B]
        field_simp [hba, hcd']
        ring
      rw [hr, map_one]
      simp only [ite_true]
    · rw [if_neg hxd, add_zero, ← map_mul]
      apply congrArg χ
      by_cases hxc : x = c
      · subst x
        simp
      · have he : e x - e c ≠ 0 := sub_ne_zero.mpr (fun h => hxc (e.injective h))
        rw [← mul_div_assoc, eq_div_iff he]
        dsimp [e, fractionalShiftEquiv, A, B]
        field_simp [hba, hcd', sub_ne_zero.mpr hxd, sub_ne_zero.mpr hxc]
        ring
  have hs := sum_congr (s₁ := (univ : Finset K)) rfl (fun x _ => hp x)
  rw [sum_add_distrib, ← mul_sum,
    e.sum_comp (fun t => χ (t * (t - 1) / (t - e c)))] at hs
  simp only [sum_ite_eq', mem_univ, if_true] at hs
  rw [hparam] at hs
  exact hs

/-- Averaging one shift over the complete field gives square-root mean cancellation. -/
theorem fourShiftCharacterSum_energy_le (χ : MulChar K ℂ) (hχ : χ ≠ 1) (a b d : K)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    ∑ c ∈ (univ : Finset K).filter (· ≠ d), ‖fourShiftCharacterSum χ a b c d + 1‖ ^ 2 ≤
      (Fintype.card K : ℝ) * ((Fintype.card K : ℝ) - 2) := by
  let A := (b - d) / (b - a)
  let B := A * (d - a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hB : B ≠ 0 := mul_ne_zero (div_ne_zero (sub_ne_zero.mpr hbd) hba)
    (sub_ne_zero.mpr (Ne.symm had))
  let e := fractionalShiftEquiv A B d hB
  have hp (c : K) (hc : c ≠ d) :
      ‖fourShiftCharacterSum χ a b c d + 1‖ ^ 2 = ‖threePointCharacterSum χ (e c)‖ ^ 2 := by
    have hparam : e c = (b - d) * (c - a) / ((b - a) * (c - d)) := by
      change A + B / (c - d) = _
      dsimp [A, B]
      field_simp [hba, sub_ne_zero.mpr hc]
      ring
    rw [fourShiftCharacterSum_crossRatio χ a b c d hab had hbd hc, ← hparam,
      norm_mul, mul_pow, character_norm_sq,
      if_neg (div_ne_zero hba (sub_ne_zero.mpr hc)), one_mul]
  calc
    _ = ∑ c ∈ (univ : Finset K).filter (· ≠ d), ‖threePointCharacterSum χ (e c)‖ ^ 2 :=
      sum_congr rfl (fun c hc => hp c (mem_filter.mp hc).2)
    _ ≤ ∑ c : K, ‖threePointCharacterSum χ (e c)‖ ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun c _ _ => sq_nonneg _)
    _ = ∑ t : K, ‖threePointCharacterSum χ t‖ ^ 2 := e.sum_comp _
    _ ≤ _ := threePointCharacterSum_energy_le χ hχ

end Finite

end RHTower.QuasiRHShiftCorrelation
