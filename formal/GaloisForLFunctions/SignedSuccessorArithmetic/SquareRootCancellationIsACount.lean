import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Square-root cancellation is a count: the calibration over finite fields

Over a finite field `F` the successor correlation of two multiplicative characters,
`S(χ, ψ) = Σ_x χ(x) ψ(x+1)`, is a Jacobi sum: `S(χ, ψ) = χ(-1) J(χ, ψ)`
(`charSuccCorr_eq_jacobiSum`). Two exact laws follow, and they are the model of the field:

* **Perfect cancellation.** For a nontrivial `χ`, `S(χ, χ⁻¹) = -1` (`charSuccCorr_inv`). For the
  quadratic character this is `Σ_x χ(x) χ(x+1) = -1`, equivalently the exact count
  `2·#{x : χ(x) χ(x+1) = 1} + 3 = q` of consecutive equal quadratic symbols
  (`two_mul_card_quadratic_succ_agree_add_three`): the successor agreement count of the pure model
  is `(q − 3)/2` with no error term.
* **Square-root cancellation as an integer.** For complex characters with `χ, ψ, χψ` nontrivial,
  `|S(χ, ψ)|² = q` (`norm_sq_charSuccCorr`): the size of the signed successor sum is the square
  root of a count.

Over `ℤ` the conductor-three twins reproduce the first law along the successor
(`TheFloorIsAttainedAtConductorThree`); what has no counterpart over `ℤ` is the second.
-/

namespace GaloisForLFunctions.SignedSuccessorArithmetic

open Finset

variable {F : Type*} [Field F] [Fintype F]

/-- The successor correlation `S(χ, ψ) = Σ_x χ(x) ψ(x+1)` of two multiplicative characters. -/
def charSuccCorr {R : Type*} [CommRing R] (χ ψ : MulChar F R) : R := ∑ x : F, χ x * ψ (x + 1)

omit [Fintype F] in
theorem mulChar_neg_one_mul_self {R : Type*} [CommRing R] (χ : MulChar F R) :
    χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- **The successor correlation is a Jacobi sum.** `S(χ, ψ) = χ(-1) J(χ, ψ)`. -/
theorem charSuccCorr_eq_jacobiSum {R : Type*} [CommRing R] (χ ψ : MulChar F R) :
    charSuccCorr χ ψ = χ (-1) * jacobiSum χ ψ := by
  have h : jacobiSum χ ψ = χ (-1) * charSuccCorr χ ψ := by
    rw [jacobiSum, charSuccCorr, mul_sum]
    refine Fintype.sum_equiv (Equiv.neg F) _ _ fun x => ?_
    simp only [Equiv.neg_apply]
    rw [show -x = -1 * x by ring, map_mul, ← mul_assoc, ← mul_assoc, mulChar_neg_one_mul_self,
      one_mul, show -1 * x + 1 = 1 - x by ring]
  rw [h, ← mul_assoc, mulChar_neg_one_mul_self, one_mul]

/-- **Perfect successor cancellation.** `S(χ, χ⁻¹) = -1` for every nontrivial character. -/
theorem charSuccCorr_inv {R : Type*} [CommRing R] [IsDomain R] {χ : MulChar F R} (hχ : χ ≠ 1) :
    charSuccCorr χ χ⁻¹ = -1 := by
  rw [charSuccCorr_eq_jacobiSum, jacobiSum_nontrivial_inv hχ, mul_neg, mulChar_neg_one_mul_self]

variable [DecidableEq F]

/-- The quadratic character has successor correlation `-1`. -/
theorem quadraticChar_succCorr (hF : ringChar F ≠ 2) :
    ∑ x : F, quadraticChar F x * quadraticChar F (x + 1) = -1 := by
  have h := charSuccCorr_inv (quadraticChar_ne_one hF)
  rwa [(quadraticChar_isQuadratic F).inv] at h

/-- The product `χ(x) χ(x+1)` of quadratic symbols takes the values `1, -1` off `{0, -1}` and `0`
on it. -/
theorem quadratic_succ_trichotomy (x : F) :
    (quadraticChar F x * quadraticChar F (x + 1) = 1 ∨
      quadraticChar F x * quadraticChar F (x + 1) = -1) ∨
      (quadraticChar F x * quadraticChar F (x + 1) = 0 ∧ (x = 0 ∨ x = -1)) := by
  by_cases h0 : x = 0
  · right; simp [h0]
  by_cases h1 : x + 1 = 0
  · right
    refine ⟨by simp [h1], Or.inr (eq_neg_of_add_eq_zero_left h1)⟩
  left
  rcases quadraticChar_dichotomy h0 with ha | ha <;>
    rcases quadraticChar_dichotomy h1 with hb | hb <;> simp [ha, hb]

/-- **The exact successor count of the pure model.** For odd `q`, the number of `x ∈ F` with
`χ(x) = χ(x+1) ≠ 0` is `(q − 3)/2`. -/
theorem two_mul_card_quadratic_succ_agree_add_three (hF : ringChar F ≠ 2) :
    2 * (univ.filter fun x : F => quadraticChar F x * quadraticChar F (x + 1) = 1).card + 3 =
      Fintype.card F := by
  set g : F → ℤ := fun x => quadraticChar F x * quadraticChar F (x + 1) with hg
  have hval : ∀ x, g x = (if g x = 1 then 1 else 0) - (if g x = -1 then 1 else 0) := by
    intro x
    rcases quadratic_succ_trichotomy x with (h | h) | ⟨h, _⟩
    · have h' : g x = 1 := h; rw [h']; norm_num
    · have h' : g x = -1 := h; rw [h']; norm_num
    · have h' : g x = 0 := h; rw [h']; norm_num
  have hone : ∀ x : F, (1 : ℤ) = (if g x = 1 then 1 else 0) + (if g x = -1 then 1 else 0) +
      (if x = 0 ∨ x = -1 then 1 else 0) := by
    intro x
    rcases quadratic_succ_trichotomy x with (h | h) | ⟨h, hx⟩
    · have : ¬ (x = 0 ∨ x = -1) := by
        rintro (rfl | rfl) <;> simp at h
      have h' : g x = 1 := h
      rw [h', if_neg this]; norm_num
    · have : ¬ (x = 0 ∨ x = -1) := by
        rintro (rfl | rfl) <;> simp at h
      have h' : g x = -1 := h
      rw [h', if_neg this]; norm_num
    · have h' : g x = 0 := h
      rw [h', if_pos hx]; norm_num
  have hsum := quadraticChar_succCorr hF
  have hS : ∑ x, g x = ((univ.filter fun x => g x = 1).card : ℤ) -
      (univ.filter fun x => g x = -1).card := by
    rw [sum_congr rfl fun x _ => hval x, sum_sub_distrib, sum_boole, sum_boole]
  have hC : (Fintype.card F : ℤ) = ((univ.filter fun x => g x = 1).card : ℤ) +
      (univ.filter fun x => g x = -1).card + (univ.filter fun x : F => x = 0 ∨ x = -1).card := by
    rw [← card_univ, show ((univ : Finset F).card : ℤ) = ∑ _x : F, (1 : ℤ) by simp,
      sum_congr rfl fun x _ => hone x, sum_add_distrib, sum_add_distrib, sum_boole, sum_boole,
      sum_boole]
  have h2 : (univ.filter fun x : F => x = 0 ∨ x = -1).card = 2 := by
    have hne : (0 : F) ≠ -1 := by simp
    rw [show (univ.filter fun x : F => x = 0 ∨ x = -1) = {0, -1} by ext; simp]
    exact card_pair hne
  rw [h2] at hC
  have hS' : ∑ x, g x = -1 := hsum
  have : (2 * ((univ.filter fun x => g x = 1).card : ℤ)) + 3 = Fintype.card F := by
    rw [hC]; push_cast; linarith
  exact_mod_cast this

omit [DecidableEq F] in
/-- For complex characters, the inverse pair has conjugate Jacobi sum. -/
theorem jacobiSum_inv_inv_eq_star (χ ψ : MulChar F ℂ) :
    jacobiSum χ⁻¹ ψ⁻¹ = star (jacobiSum χ ψ) := by
  rw [jacobiSum, jacobiSum, star_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [star_mul', MulChar.star_apply', MulChar.star_apply']

omit [DecidableEq F] in
/-- **Square-root cancellation is a count.** For complex characters with `χ`, `ψ` and `χψ`
nontrivial, `|Σ_x χ(x) ψ(x+1)|² = q`. -/
theorem norm_sq_charSuccCorr {χ ψ : MulChar F ℂ} (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ * ψ ≠ 1) :
    ‖charSuccCorr χ ψ‖ ^ 2 = Fintype.card F := by
  have hchar : ringChar ℂ ≠ ringChar F := by
    rw [ringChar.eq_zero]; exact (CharP.ringChar_ne_zero_of_finite F).symm
  have hJ := jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ
  rw [jacobiSum_inv_inv_eq_star] at hJ
  have hn1 : ‖χ (-1)‖ = 1 := by
    have h := congrArg norm (mulChar_neg_one_mul_self χ)
    rw [norm_mul, norm_one] at h
    nlinarith [norm_nonneg (χ (-1))]
  rw [charSuccCorr_eq_jacobiSum, norm_mul, hn1, one_mul]
  have hns : (‖jacobiSum χ ψ‖ ^ 2 : ℝ) = (jacobiSum χ ψ * star (jacobiSum χ ψ)).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hns, hJ]
  simp

end GaloisForLFunctions.SignedSuccessorArithmetic
