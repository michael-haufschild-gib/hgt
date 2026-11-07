import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.PrimitiveProductCollisionCosts
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheRectangularMomentsHaveAnArithmeticCost

/-!
# Arithmetic moments on arbitrary smooth heads

A smooth head needs no dyadic support restriction. For each row pair `m,n`,
the reduced quotients `m/gcd(m,n)` and `n/gcd(m,n)` control the cumulative
product collisions. Their weighted sum is `primitiveHeadCost`.

The triangular Fourier majorant transfers actual logarithmic energy to
mean squares on every centered interval. Smooth–rough uniqueness retains
the exact coefficient diagonal. For prime-tail powers, the coefficient
supremum and squared sum supply the factorial moment bounds. Restricting
to a large-tail event divides by its moment threshold.
-/

noncomputable section
open Finset MeasureTheory
namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
open RHTower.Sieve

private def positiveProductFrequency (p : ℕ × ℕ) : ℝ :=
  Real.log (p.1 * p.2 : ℕ) / (2 * Real.pi)

private theorem finiteFrequencyPoly_eq_product (A B : Finset ℕ)
    (r b : ℕ → ℂ) (t : ℝ) :
    finiteFrequencyPoly (fun p => r p.1 * b p.2) (A ×ˢ B) positiveProductFrequency t =
      indexedPoly (A ×ˢ B) (fun p => p.1 * p.2) (fun p => r p.1 * b p.2) t := by
  unfold finiteFrequencyPoly indexedPoly
  apply sum_congr rfl
  intro p _
  have he : 2 * Real.pi * (t * positiveProductFrequency p) = t * Real.log (p.1 * p.2 : ℕ) := by
    dsimp only [positiveProductFrequency]
    field_simp
  rw [he]

private theorem positiveProductFrequency_close (p q : ℕ × ℕ) {T : ℝ}
    (hclose : |positiveProductFrequency p - positiveProductFrequency q| < 1 / (2 * Real.pi * T)) :
    |Real.log (p.1 * p.2 : ℕ) - Real.log (q.1 * q.2 : ℕ)| ≤ 1 / T := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have he : |positiveProductFrequency p - positiveProductFrequency q| =
      |Real.log (p.1 * p.2 : ℕ) - Real.log (q.1 * q.2 : ℕ)| / (2 * Real.pi) := by
    dsimp only [positiveProductFrequency]
    rw [← sub_div, abs_div, abs_of_pos hpi]
  have hd : 1 / (2 * Real.pi * T) = (1 / T) / (2 * Real.pi) := by ring
  rw [he, hd] at hclose
  exact ((div_lt_div_iff_of_pos_right hpi).mp hclose).le

private theorem product_frequency_weight_le (A B : Finset ℕ) (r b : ℕ → ℂ) {T : ℝ} :
    finiteFrequencyCollisionWeight (fun p => r p.1 * b p.2) (A ×ˢ B)
      positiveProductFrequency (1 / (2 * Real.pi * T)) ≤ rectangularLogWeight A B r b (1 / T) := by
  unfold finiteFrequencyCollisionWeight rectangularLogWeight
  simp only [sum_product]
  apply sum_le_sum
  intro m hm
  rw [sum_comm (s := B) (t := A)]
  apply sum_le_sum
  intro n hn
  rw [mul_sum]
  apply sum_le_sum
  intro p hp
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  by_cases hc : |positiveProductFrequency (m,p) - positiveProductFrequency (n,q)| < 1 / (2 * Real.pi * T)
  · rw [if_pos hc, if_pos (positiveProductFrequency_close (m,p) (n,q) hc)]
    simp only [norm_mul]
    exact le_of_eq (by ring)
  · rw [if_neg hc]
    split_ifs <;> positivity

private def translatedHeadCoeff (c : ℕ → ℂ) (U : ℝ) (n : ℕ) : ℂ :=
  c n * Complex.exp (((U * Real.log n : ℝ) : ℂ) * Complex.I)

private theorem norm_translatedHeadCoeff (c : ℕ → ℂ) (U : ℝ) (n : ℕ) : ‖translatedHeadCoeff c U n‖ = ‖c n‖ := by
  rw [translatedHeadCoeff, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

private theorem headPoly_translatedHeadCoeff (A : Finset ℕ) (c : ℕ → ℂ) (U t : ℝ) :
    headPoly A (translatedHeadCoeff c U) t = headPoly A c (U + t) := by
  unfold headPoly
  apply sum_congr rfl
  intro n _
  dsimp only [translatedHeadCoeff]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem weighted_smooth_rough_log_row_le {y m n Z : ℕ} {B : Finset ℕ}
    (hms : m ∈ Nat.smoothNumbers y) (hns : n ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, IsRough y p) (hZ : ∀ p ∈ B, p ≤ Z)
    (b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ p ∈ B, ‖b p‖ ≤ K)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ p ∈ B, ∑ q ∈ B,
      if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ then ‖b p‖ * ‖b q‖ else 0) ≤
      (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) +
        ((rectangularOffDiagonalLogFiber m n Z δ).card : ℝ) * K ^ 2 := by
  let D := rectangularOffDiagonalLogFiber m n Z δ
  have hpoint (p q : ℕ) (hp : p ∈ B) (hq : q ∈ B) :
      (if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ then ‖b p‖ * ‖b q‖ else 0) ≤
      (if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) +
        (if (p,q) ∈ D then K ^ 2 else 0) := by
    by_cases he : m * p = n * q
    · obtain ⟨hmn, hpq⟩ := smooth_mul_rough_injective hms hns (hB p hp) (hB q hq) he
      subst n
      subst q
      simp only [sub_self, abs_zero, if_pos hδ, if_true]
      have hnon : 0 ≤ (if (p,p) ∈ D then K ^ 2 else 0) := by split_ifs <;> positivity
      nlinarith only [hnon]
    · by_cases hc : |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ δ
      · have hmem : (p,q) ∈ D := mem_filter.mpr ⟨mem_product.mpr
          ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hB p hp).1, hZ p hp⟩,
            mem_Icc.mpr ⟨Nat.pos_of_ne_zero (hB q hq).1, hZ q hq⟩⟩, he, hc⟩
        rw [if_pos hc, if_pos hmem]
        have hd : 0 ≤ (if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) := by
          split_ifs <;> positivity
        have hw := mul_le_mul (hb p hp) (hb q hq) (norm_nonneg _) hK
        nlinarith only [hw, hd]
      · rw [if_neg hc]
        split_ifs <;> positivity
  have hdiag : (∑ p ∈ B, ∑ q ∈ B,
      if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) =
      if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0 := by
    by_cases h : m = n <;> simp [h]
  have hoff : (∑ p ∈ B, ∑ q ∈ B, if (p,q) ∈ D then K ^ 2 else 0) ≤
      ((rectangularOffDiagonalLogFiber m n Z δ).card : ℝ) * K ^ 2 := by
    have hsub : ((B ×ˢ B).filter fun p => p ∈ D) ⊆ D := by
      intro p hp
      exact (mem_filter.mp hp).2
    have hc : (((B ×ˢ B).filter fun p => p ∈ D).card : ℝ) ≤
        ((rectangularOffDiagonalLogFiber m n Z δ).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    have he : (∑ p ∈ B, ∑ q ∈ B, if (p,q) ∈ D then K ^ 2 else 0) =
        ∑ p ∈ B ×ˢ B, if p ∈ D then K ^ 2 else 0 :=
      (sum_product B B (fun p : ℕ × ℕ => if p ∈ D then K ^ 2 else 0)).symm
    rw [he, ← sum_filter]
    simpa only [sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg K)
  calc
    _ ≤ ∑ p ∈ B, ∑ q ∈ B, ((if m = n then if p = q then ‖b p‖ ^ 2 else 0 else 0) +
        (if (p,q) ∈ D then K ^ 2 else 0)) :=
      sum_le_sum fun p hp => sum_le_sum fun q hq => hpoint p q hp hq
    _ = (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) +
        ∑ p ∈ B, ∑ q ∈ B, if (p,q) ∈ D then K ^ 2 else 0 := by
      simp only [sum_add_distrib, hdiag]
    _ ≤ _ := add_le_add le_rfl hoff

/-- Positive-support products are controlled by their actual weighted logarithmic energy. -/
theorem integral_head_tail_le_logWeight (A B : Finset ℕ) (r b : ℕ → ℂ)
    (hA : ∀ m ∈ A, m ≠ 0) (hB : ∀ p ∈ B, p ≠ 0) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) ≤
      (5 * Real.pi / 2) * T * rectangularLogWeight A B r b (1 / T) := by
  have hδ : 0 < 1 / (2 * Real.pi * T) := by positivity
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * T)) * T ≤ 1 := by
    field_simp
    exact le_rfl
  have h := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (fun p => r p.1 * b p.2) (A ×ˢ B) positiveProductFrequency hδ hscale
  simp_rw [finiteFrequencyPoly_eq_product, ← headPoly_mul A B r b hA hB, norm_mul, mul_pow] at h
  apply h.trans
  calc
    _ ≤ (5 / (4 * (1 / (2 * Real.pi * T)))) * rectangularLogWeight A B r b (1 / T) :=
      mul_le_mul_of_nonneg_left (product_frequency_weight_le A B r b) (by positivity)
    _ = _ := by field_simp; ring

/-- The exact logarithmic-energy transfer is uniform in the center of the height interval. -/
theorem integral_head_tail_shift_le_logWeight (A B : Finset ℕ) (r b : ℕ → ℂ)
    (hA : ∀ m ∈ A, m ≠ 0) (hB : ∀ p ∈ B, p ≠ 0) (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ 2) ≤
      (5 * Real.pi / 2) * T * rectangularLogWeight A B r b (1 / T) := by
  have h := integral_head_tail_le_logWeight A B (translatedHeadCoeff r U) (translatedHeadCoeff b U) hA hB hT
  simpa only [headPoly_translatedHeadCoeff, rectangularLogWeight, norm_translatedHeadCoeff] using h

/-- The head coefficient cost retains the gcd of each actual pair of integer frequencies. -/
def primitiveHeadCost (A : Finset ℕ) (r : ℕ → ℂ) (Z : ℕ) : ℝ :=
  ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ * primitiveProductCost m n Z

/-- A weighted first moment bounds the primitive arithmetic cost without a dyadic restriction. -/
theorem primitiveHeadCost_le_first_moment (A : Finset ℕ) (r : ℕ → ℂ) (Z : ℕ) :
    primitiveHeadCost A r Z ≤ 2 * (Z : ℝ) ^ 2 * (∑ m ∈ A, ‖r m‖) ^ 2 +
      2 * (Z : ℝ) * (∑ m ∈ A, ‖r m‖) * (∑ m ∈ A, (m : ℝ) * ‖r m‖) := by
  have he (m n : ℕ) : ‖r m‖ * ‖r n‖ * (2 * (Z : ℝ) ^ 2 + (Z : ℝ) * (m+n)) =
      (2 * (Z : ℝ) ^ 2 * ‖r m‖) * ‖r n‖ +
        ((Z : ℝ) * ((m : ℝ) * ‖r m‖)) * ‖r n‖ +
        ((Z : ℝ) * ‖r m‖) * ((n : ℝ) * ‖r n‖) := by ring
  calc
    _ ≤ ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
        (2 * (Z : ℝ) ^ 2 + (Z : ℝ) * (m+n)) :=
      sum_le_sum fun m _ => sum_le_sum fun n _ =>
        mul_le_mul_of_nonneg_left (primitiveProductCost_le m n Z)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [he, sum_add_distrib, ← mul_sum, ← sum_mul]
      ring

/-- Actual weighted log-energy has a primitive-step error for any finite smooth head. -/
theorem scaled_rectangularLogWeight_le_primitive {y Z : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y) (hB : ∀ p ∈ B, IsRough y p)
    (hZ : ∀ p ∈ B, p ≤ Z) (r b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ p ∈ B, ‖b p‖ ≤ K) {T : ℝ} (hT : 0 < T) :
    T * rectangularLogWeight A B r b (1 / T) ≤
      T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) + primitiveHeadCost A r Z * K ^ 2 := by
  have hrow (m n : ℕ) (hm : m ∈ A) (hn : n ∈ A) :
      T * (∑ p ∈ B, ∑ q ∈ B,
        if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ 1 / T then ‖b p‖ * ‖b q‖ else 0) ≤
      T * (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) + primitiveProductCost m n Z * K ^ 2 := by
    have h := weighted_smooth_rough_log_row_le (hA m hm) (hA n hn) hB hZ b hK hb
      (by positivity : 0 ≤ 1 / T)
    have hc := mul_card_rectangularOffDiagonalLogFiber_le_primitive
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hA m hm)))
      (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers (hA n hn))) hT (Z := Z)
    calc
      _ ≤ T * ((if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) +
          ((rectangularOffDiagonalLogFiber m n Z (1 / T)).card : ℝ) * K ^ 2) :=
        mul_le_mul_of_nonneg_left h hT.le
      _ = T * (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) +
          (T * ((rectangularOffDiagonalLogFiber m n Z (1 / T)).card : ℝ)) * K ^ 2 := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (sq_nonneg K))
  have hd : (∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
      (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0)) =
      (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro m hm
    simp [mul_ite, hm, sq, mul_assoc]
  have he (m n : ℕ) : ‖r m‖ * ‖r n‖ *
      (T * (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) + primitiveProductCost m n Z * K ^ 2) =
      T * (‖r m‖ * ‖r n‖ * (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0)) +
        (‖r m‖ * ‖r n‖ * primitiveProductCost m n Z) * K ^ 2 := by ring
  calc
    _ = ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
        (T * (∑ p ∈ B, ∑ q ∈ B,
          if |Real.log (m * p : ℕ) - Real.log (n * q : ℕ)| ≤ 1 / T then ‖b p‖ * ‖b q‖ else 0)) := by
      unfold rectangularLogWeight
      rw [mul_sum]
      apply sum_congr rfl
      intro m _
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ m ∈ A, ∑ n ∈ A, ‖r m‖ * ‖r n‖ *
        (T * (if m = n then ∑ p ∈ B, ‖b p‖ ^ 2 else 0) + primitiveProductCost m n Z * K ^ 2) :=
      sum_le_sum fun m hm => sum_le_sum fun n hn =>
        mul_le_mul_of_nonneg_left (hrow m n hm hn) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [he, sum_add_distrib, ← mul_sum, ← sum_mul, hd]
      dsimp only [primitiveHeadCost]
      ring

/-- The mean-square arithmetic cost retains primitive row quotients on an arbitrary smooth support. -/
theorem integral_smooth_head_rough_tail_le_primitive {y Z : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y) (hB : ∀ p ∈ B, IsRough y p)
    (hZ : ∀ p ∈ B, p ≤ Z) (r b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ p ∈ B, ‖b p‖ ≤ K) (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ 2) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) + primitiveHeadCost A r Z * K ^ 2) := by
  have h := integral_head_tail_shift_le_logWeight A B r b
    (fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)) (fun p hp => (hB p hp).1) U hT
  calc
    _ ≤ (5 * Real.pi / 2) * T * rectangularLogWeight A B r b (1 / T) := h
    _ = (5 * Real.pi / 2) * (T * rectangularLogWeight A B r b (1 / T)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (scaled_rectangularLogWeight_le_primitive hA hB hZ r b hK hb hT) (by positivity)

/-- A first coefficient moment replaces the dyadic support restriction in smooth-head mean squares. -/
theorem integral_smooth_head_rough_tail_le_first_moment {y Z : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y) (hB : ∀ p ∈ B, IsRough y p)
    (hZ : ∀ p ∈ B, p ≤ Z) (r b : ℕ → ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ p ∈ B, ‖b p‖ ≤ K) (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ 2) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * (∑ p ∈ B, ‖b p‖ ^ 2) +
          (2 * (Z : ℝ) ^ 2 * (∑ m ∈ A, ‖r m‖) ^ 2 +
            2 * (Z : ℝ) * (∑ m ∈ A, ‖r m‖) * (∑ m ∈ A, (m : ℝ) * ‖r m‖)) * K ^ 2) := by
  apply (integral_smooth_head_rough_tail_le_primitive hA hB hZ r b hK hb U hT).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (primitiveHeadCost_le_first_moment A r Z) (sq_nonneg K))

/-- Higher prime-tail moments retain the primitive row-pair cost on every smooth head. -/
theorem integral_smooth_head_prime_tail_pow_le_primitive {y Y : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ (2*k)) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2) := by
  have hrough : ∀ q ∈ powSupport B k, IsRough y q :=
    powSupport_rough (fun p hp => isRough_of_prime (hB p hp).1 (hB p hp).2) k
  have hcoef : ∀ q ∈ powSupport B k, ‖powCoeff B b k q‖ ≤ (k.factorial : ℝ) :=
    norm_powCoeff_le_factorial (fun p hp => (hB p hp).1) b hb k
  have h := integral_smooth_head_rough_tail_le_primitive hA hrough (powSupport_le hY k)
    r (powCoeff B b k) (by positivity : 0 ≤ (k.factorial : ℝ)) hcoef U hT
  have hpoly (t : ℝ) : ‖headPoly (powSupport B k) (powCoeff B b k) (U+t)‖ ^ 2 =
      ‖headPoly B b (U+t)‖ ^ (2*k) := by
    rw [← headPoly_pow b (fun p hp => (hB p hp).1.ne_zero) (U+t) k, norm_pow,
      ← pow_mul, mul_comm k 2]
  simp only [hpoly] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left (powNorm_le (fun p hp => (hB p hp).1) b k)
    (by positivity : 0 ≤ T * ∑ m ∈ A, ‖r m‖ ^ 2)

/-- A first head coefficient moment controls every bounded prime-tail power. -/
theorem integral_smooth_head_prime_tail_pow_le_first_moment {y Y : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (U : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Icc (-T) T, ‖headPoly A r (U+t)‖ ^ 2 * ‖headPoly B b (U+t)‖ ^ (2*k)) ≤
      (5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          (2 * ((Y : ℝ) ^ k) ^ 2 * (∑ m ∈ A, ‖r m‖) ^ 2 +
            2 * (Y : ℝ) ^ k * (∑ m ∈ A, ‖r m‖) * (∑ m ∈ A, (m : ℝ) * ‖r m‖)) *
              (k.factorial : ℝ) ^ 2) := by
  apply (integral_smooth_head_prime_tail_pow_le_primitive hA hB hY r b hb k U hT).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  have h := primitiveHeadCost_le_first_moment A r (Y ^ k)
  simp only [Nat.cast_pow] at h
  exact mul_le_mul_of_nonneg_right h (sq_nonneg _)

/-- The literal full smooth head and prime tail obey the unrestricted arithmetic moment bound. -/
theorem integral_full_smooth_head_prime_tail_pow_le (M y Y k : ℕ) (U : ℝ) {T : ℝ} (hT : 0 < T) :
    let A := (Icc 1 M).filter fun m => m ∈ Nat.smoothNumbers y
    let B := (Icc y Y).filter Nat.Prime
    (∫ t in Set.Icc (-T) T, ‖headPoly A (fun _ => 1) (U+t)‖ ^ 2 *
        ‖headPoly B (fun _ => 1) (U+t)‖ ^ (2*k)) ≤
      (5 * Real.pi / 2) *
        (T * (A.card : ℝ) * ((k.factorial : ℝ) * (B.card : ℝ) ^ k) +
          (2 * ((Y : ℝ) ^ k) ^ 2 * (A.card : ℝ) ^ 2 +
            2 * (Y : ℝ) ^ k * A.card * (∑ m ∈ A, (m : ℝ))) * (k.factorial : ℝ) ^ 2) := by
  dsimp only
  let A := (Icc 1 M).filter fun m => m ∈ Nat.smoothNumbers y
  let B := (Icc y Y).filter Nat.Prime
  have hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y := fun m hm => (mem_filter.mp hm).2
  have hB : ∀ p ∈ B, p.Prime ∧ y ≤ p := fun p hp =>
    ⟨(mem_filter.mp hp).2, (mem_Icc.mp (mem_filter.mp hp).1).1⟩
  have hY : ∀ p ∈ B, p ≤ Y := fun p hp => (mem_Icc.mp (mem_filter.mp hp).1).2
  have h := integral_smooth_head_prime_tail_pow_le_first_moment hA hB hY
    (fun _ => 1) (fun _ => 1) (by intro p hp; simp) k U hT
  simpa only [norm_one, one_pow, sum_const, nsmul_eq_mul, mul_one] using h

/-- Large prime-tail events pay their full moment threshold under smooth-head weight. -/
theorem setIntegral_smooth_head_on_large_prime_tail_le {y Y : ℕ} {A B : Finset ℕ}
    (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (hY : ∀ p ∈ B, p ≤ Y)
    (r b : ℕ → ℂ) (hb : ∀ p ∈ B, ‖b p‖ ≤ 1) (k : ℕ)
    (U : ℝ) {T V : ℝ} (hT : 0 < T) (hV : 0 < V) :
    (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖headPoly B b (U+t)‖},
        ‖headPoly A r (U+t)‖ ^ 2) ≤
      ((5 * Real.pi / 2) *
        (T * (∑ m ∈ A, ‖r m‖ ^ 2) * ((k.factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) +
          primitiveHeadCost A r (Y ^ k) * (k.factorial : ℝ) ^ 2)) / V ^ (2*k) := by
  let R (t : ℝ) := headPoly A r (U+t)
  let Q (t : ℝ) := headPoly B b (U+t)
  have hcR : Continuous R := (continuous_headPoly A r).comp (continuous_const.add continuous_id)
  have hcQ : Continuous Q := (continuous_headPoly B b).comp (continuous_const.add continuous_id)
  let g (t : ℝ) := (‖R t‖ ^ 2 * ‖Q t‖ ^ (2*k)) / V ^ (2*k)
  have hgc : Continuous g := ((hcR.norm.pow 2).mul (hcQ.norm.pow (2*k))).div_const _
  have hclosed : IsClosed {t | V ≤ ‖Q t‖} := isClosed_le continuous_const hcQ.norm
  have hcompact : IsCompact (Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}) := isCompact_Icc.inter_right hclosed
  have hmeas : MeasurableSet (Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}) :=
    measurableSet_Icc.inter hclosed.measurableSet
  have h1 : (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, ‖R t‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, g t := by
    apply setIntegral_mono_on ((hcR.norm.pow 2).continuousOn.integrableOn_compact hcompact)
      (hgc.continuousOn.integrableOn_compact hcompact) hmeas
    intro t ht
    dsimp only [g]
    apply (le_div_iff₀ (by positivity : 0 < V ^ (2*k))).mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hV.le ht.2 (2*k)) (sq_nonneg _)
  have h2 : (∫ t in Set.Icc (-T) T ∩ {t | V ≤ ‖Q t‖}, g t) ≤
      ∫ t in Set.Icc (-T) T, g t :=
    setIntegral_mono_set hgc.integrableOn_Icc (Filter.Eventually.of_forall fun t => by
      dsimp only [g]; positivity) (Filter.Eventually.of_forall Set.inter_subset_left)
  have h3 : (∫ t in Set.Icc (-T) T, g t) =
      (∫ t in Set.Icc (-T) T, ‖R t‖ ^ 2 * ‖Q t‖ ^ (2*k)) / V ^ (2*k) := by
    dsimp only [g]
    rw [MeasureTheory.integral_div]
  have h4 := div_le_div_of_nonneg_right
    (integral_smooth_head_prime_tail_pow_le_primitive hA hB hY r b hb k U hT)
    (by positivity : 0 ≤ V ^ (2*k))
  exact h1.trans (h2.trans (h3.trans_le h4))

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
