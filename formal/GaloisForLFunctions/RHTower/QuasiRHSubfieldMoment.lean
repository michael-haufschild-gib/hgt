import GaloisForLFunctions.RHTower.QuasiRHCharacterCorrelation
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Positivity

/-!
# Subfield concentration in the additive-shift fourth moment

Norm surjectivity forces a character to be trivial on a subfield when its
order divides the norm exponent. The subfield then contributes an explicit
positive term to the fourth moment. Quadratic extensions in characteristic
five realize this obstruction with characters of exact order six.
-/

noncomputable section

namespace RHTower.QuasiRHShiftCorrelation

open Finset
open scoped Classical

variable {F K : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]

omit [Fintype F] in
/-- The norm exponent detects characters trivial on the embedded subfield. -/
theorem character_algebraMap_of_dvd_normIndex (χ : MulChar K ℂ) {m : ℕ}
    (hm : m ≠ 0) (hχ : χ ^ m = 1)
    (hindex : m ∣ (Nat.card K - 1) / (Nat.card F - 1)) {a : F} (ha : a ≠ 0) :
    χ (algebraMap F K a) = 1 := by
  obtain ⟨y, hy⟩ := FiniteField.norm_surjective F K a
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    exact ha (by simpa using hy.symm)
  obtain ⟨j, hj⟩ := hindex
  rw [← hy, FiniteField.algebraMap_norm_eq_pow, hj, pow_mul, map_pow, map_pow]
  have hp : χ y ^ m = 1 := by
    rw [← MulChar.pow_apply' χ hm, hχ, MulChar.one_apply (isUnit_iff_ne_zero.mpr hy0)]
  rw [hp, one_pow]

omit [Fintype F] [Fintype K] in
/-- On the subfield the shift packet counts all shifts except its possible zero. -/
theorem subfield_shiftPacket (χ : MulChar K ℂ)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1) (S : Finset F) (x : F) :
    ∑ a ∈ S.image (algebraMap F K), χ (algebraMap F K x - a) =
      (S.card : ℂ) - if x ∈ S then 1 else 0 := by
  rw [sum_image (fun a _ b _ h => (algebraMap F K).injective h)]
  have hp (a : F) : χ (algebraMap F K x - algebraMap F K a) =
      1 - if a = x then 1 else 0 := by
    by_cases ha : a = x
    · simp [ha, MulChar.map_zero]
    · rw [← map_sub, hχ (x - a) (sub_ne_zero.mpr (Ne.symm ha)), if_neg ha, sub_zero]
  simp_rw [hp]
  rw [sum_sub_distrib]
  simp

omit [Fintype K] in
/-- Exact contribution from the embedded subfield, including the shifts themselves. -/
theorem subfield_shiftFourthMoment_contribution (χ : MulChar K ℂ)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1) (S : Finset F) :
    ∑ x : F, ‖∑ a ∈ S.image (algebraMap F K), χ (algebraMap F K x - a)‖ ^ 4 =
      ((Fintype.card F : ℝ) - S.card) * (S.card : ℝ) ^ 4 +
        S.card * ((S.card : ℝ) - 1) ^ 4 := by
  have hp (x : F) :
      ‖∑ a ∈ S.image (algebraMap F K), χ (algebraMap F K x - a)‖ ^ 4 =
        if x ∈ S then ((S.card : ℝ) - 1) ^ 4 else (S.card : ℝ) ^ 4 := by
    rw [subfield_shiftPacket χ hχ]
    by_cases hx : x ∈ S
    · rw [if_pos hx, if_pos hx]
      have hc : 0 ≤ (S.card : ℝ) - 1 := by
        have hc' : (1 : ℝ) ≤ S.card := by
          exact_mod_cast (show 1 ≤ S.card from card_pos.mpr ⟨x, hx⟩)
        linarith
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    · simp [hx]
  simp_rw [hp]
  have hsplit (x : F) :
      (if x ∈ S then ((S.card : ℝ) - 1) ^ 4 else (S.card : ℝ) ^ 4) =
        (S.card : ℝ) ^ 4 +
          if x ∈ S then ((S.card : ℝ) - 1) ^ 4 - (S.card : ℝ) ^ 4 else 0 := by
    split_ifs <;> ring
  simp_rw [hsplit, sum_add_distrib, sum_ite_mem]
  simp only [univ_inter, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- Restricting a nonnegative fourth moment to the subfield gives a sharp local lower bound. -/
theorem subfield_shiftFourthMoment_lower (χ : MulChar K ℂ)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1) (S : Finset F) :
    ((Fintype.card F : ℝ) - S.card) * (S.card : ℝ) ^ 4 +
      S.card * ((S.card : ℝ) - 1) ^ 4 ≤
        shiftFourthMoment χ (S.image (algebraMap F K)) := by
  rw [← subfield_shiftFourthMoment_contribution χ hχ]
  let f : K → ℝ := fun x => ‖∑ a ∈ S.image (algebraMap F K), χ (x - a)‖ ^ 4
  change (∑ x : F, f (algebraMap F K x)) ≤ ∑ x : K, f x
  rw [← sum_image (fun a _ b _ h => (algebraMap F K).injective h)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
    (fun x _ _ => pow_nonneg (norm_nonneg _) _)

private theorem square_normIndex (r : ℕ) (hr : 1 < r) :
    (r ^ 2 - 1) / (r - 1) = r + 1 := by
  have h1 : 1 ≤ r := hr.le
  have h2 : 1 ≤ r ^ 2 := by nlinarith
  have hprod : r ^ 2 - 1 = (r + 1) * (r - 1) := by
    nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  rw [hprod, Nat.mul_div_cancel _ (Nat.sub_pos_of_lt hr)]

/-- Sextic characters on these quadratic extensions are trivial on the base field. -/
theorem sextic_quadratic_restriction (χ : MulChar K ℂ) (hχ : χ ^ 6 = 1)
    (hcard : Nat.card K = Nat.card F ^ 2) (hmod : 6 ∣ Nat.card F + 1)
    {a : F} (ha : a ≠ 0) : χ (algebraMap F K a) = 1 := by
  apply character_algebraMap_of_dvd_normIndex χ (by norm_num) hχ _ ha
  rwa [hcard, square_normIndex _ Finite.one_lt_card]

/-- These quadratic extensions contain an exact order-six character with trivial restriction. -/
theorem exists_sextic_quadratic_character
    (hcard : Nat.card K = Nat.card F ^ 2) (hmod : 6 ∣ Nat.card F + 1) :
    ∃ χ : MulChar K ℂ, orderOf χ = 6 ∧
      ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1 := by
  have hr : 1 < Nat.card F := Finite.one_lt_card
  have h1 : 1 ≤ Nat.card F := hr.le
  have h2 : 1 ≤ Nat.card F ^ 2 := by nlinarith
  have hprod : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
    nlinarith [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2]
  have hdiv : 6 ∣ Fintype.card K - 1 := by
    rw [Fintype.card_eq_nat_card, hcard, hprod]
    exact dvd_mul_of_dvd_left hmod _
  obtain ⟨χ, horder⟩ := MulChar.exists_mulChar_orderOf K hdiv
    (Complex.isPrimitiveRoot_exp 6 (by norm_num))
  refine ⟨χ, horder, fun a ha => sextic_quadratic_restriction χ ?_ hcard hmod ha⟩
  simpa only [horder] using pow_orderOf_eq_one χ

private theorem five_odd_cubic_mod_six (n : ℕ) : 5 ^ (6 * n + 3) % 6 = 5 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have he : 6 * (n + 1) + 3 = (6 * n + 3) + 6 := by omega
    rw [he, pow_add, Nat.mul_mod, ih]
    norm_num

/-- An explicit unbounded family at `B³=q` defeats a cardinality-only fourth-moment bound. -/
theorem exists_sextic_subfield_moment_obstruction (n : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (χ : MulChar K ℂ) (S : Finset K),
      Fintype.card K = 5 ^ (12 * n + 6) ∧ S.card = 5 ^ (4 * n + 2) ∧
        orderOf χ = 6 ∧
        4 * (5 : ℝ) ^ (2 * n) * (Fintype.card K : ℝ) * (S.card : ℝ) ^ 2 ≤
          shiftFourthMoment χ S := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let F := GaloisField 5 (6 * n + 3)
  let K := FiniteField.Extension F 5 2
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card F = 5 ^ (6 * n + 3) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 5 _ (by omega)
  have hK : Nat.card K = Nat.card F ^ 2 := FiniteField.natCard_extension F 5 2
  have hmod : 6 ∣ Nat.card F + 1 := by
    rw [← Fintype.card_eq_nat_card, hF]
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, five_odd_cubic_mod_six]
  obtain ⟨χ, horder, hrestrict⟩ := exists_sextic_quadratic_character hK hmod
  have hB : 5 ^ (4 * n + 2) ≤ (univ : Finset F).card := by
    rw [card_univ, hF]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨S, _, hS⟩ := exists_subset_card_eq hB
  let T := S.image (algebraMap F K)
  have hT : T.card = 5 ^ (4 * n + 2) := by
    rw [card_image_of_injective _ (algebraMap F K).injective, hS]
  have hK' : Fintype.card K = 5 ^ (12 * n + 6) := by
    rw [Fintype.card_eq_nat_card, hK, ← Fintype.card_eq_nat_card, hF, ← pow_mul]
    congr 1
    omega
  refine ⟨K, inferInstance, inferInstance, χ, T, hK', hT, horder, ?_⟩
  let t : ℝ := 5 ^ (2 * n + 1)
  have ht : (5 : ℝ) ≤ t := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5)
        (by omega : 1 ≤ 2 * n + 1))
  have hSr : (S.card : ℝ) = t ^ 2 := by
    rw [hS, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [t]
    rw [← pow_mul]
    congr 1
    omega
  have hFr : (Fintype.card F : ℝ) = t ^ 3 := by
    rw [hF, Nat.cast_pow, Nat.cast_ofNat]
    dsimp [t]
    rw [← pow_mul]
    congr 1
    omega
  have hKr : (Fintype.card K : ℝ) = t ^ 6 := by
    rw [hK', Nat.cast_pow, Nat.cast_ofNat]
    dsimp [t]
    rw [← pow_mul]
    congr 1
    omega
  have hTr : (T.card : ℝ) = t ^ 2 := by rw [hT, ← hS]; exact hSr
  have hcoefficient : 4 * (5 : ℝ) ^ (2 * n) ≤ t - 1 := by
    have he : t = (5 : ℝ) ^ (2 * n) * 5 := by dsimp [t]; rw [pow_succ]
    nlinarith
  calc
    _ = (4 * (5 : ℝ) ^ (2 * n)) * t ^ 10 := by rw [hKr, hTr]; ring
    _ ≤ (t - 1) * t ^ 10 :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ = ((Fintype.card F : ℝ) - S.card) * (S.card : ℝ) ^ 4 := by
      rw [hFr, hSr]
      ring
    _ ≤ ((Fintype.card F : ℝ) - S.card) * (S.card : ℝ) ^ 4 +
        S.card * ((S.card : ℝ) - 1) ^ 4 := le_add_of_nonneg_right (by positivity)
    _ ≤ _ := subfield_shiftFourthMoment_lower χ hrestrict S

end RHTower.QuasiRHShiftCorrelation
