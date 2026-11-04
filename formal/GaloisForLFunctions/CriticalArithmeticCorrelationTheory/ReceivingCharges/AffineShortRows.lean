import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineMangoldtProgressions
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.MangoldtIntervalMass

/-!
# Centered affine short-row bounds

The true multiplier support combines progression mass with the exact
negative mean. Summing a coherent prime band retains both contributions.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The true multiplier support restricts a weighted affine progression without boundary loss. -/
theorem affine_supported_weight_le (p a d H X Y : ℕ) (f : ℕ → ℝ)
    {U : ℝ} (hU : 0 ≤ U) (hf : ∀ k ∈ Icc 1 Y, |f k| ≤ U)
    (hsupp : ∀ k ∈ Icc 1 Y, f k ≠ 0 → k ∈ Icc H X) :
    (∑ k ∈ (Icc 1 Y).filter (fun k => a * k ≡ d [MOD p]),
      (vonMangoldt k / (k : ℝ)) * |f k|) ≤
      U * ∑ k ∈ (Icc H X).filter (fun k => a * k ≡ d [MOD p]),
        vonMangoldt k / (k : ℝ) := by
  let S := (Icc 1 Y).filter (fun k => a * k ≡ d [MOD p])
  let T := (Icc H X).filter (fun k => a * k ≡ d [MOD p])
  have hterm (k : ℕ) (hk : k ∈ S) :
      (vonMangoldt k / (k : ℝ)) * |f k| ≤
        if k ∈ T then U * (vonMangoldt k / (k : ℝ)) else 0 := by
    obtain ⟨hkY, hcong⟩ := mem_filter.mp hk
    by_cases hkT : k ∈ T
    · rw [if_pos hkT]
      exact (mul_le_mul_of_nonneg_left (hf k hkY)
        (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))).trans_eq (mul_comm _ _)
    · have hz : f k = 0 := by
        by_contra hne
        exact hkT (mem_filter.mpr ⟨hsupp k hkY hne, hcong⟩)
      simp only [hz, abs_zero, mul_zero, if_neg hkT, le_refl]
  calc
    _ ≤ ∑ k ∈ S, if k ∈ T then U * (vonMangoldt k / (k : ℝ)) else 0 := sum_le_sum hterm
    _ = ∑ k ∈ S.filter (fun k => k ∈ T), U * (vonMangoldt k / (k : ℝ)) := by
      conv_rhs => rw [sum_filter]
    _ ≤ ∑ k ∈ T, U * (vonMangoldt k / (k : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg (fun k hk => (mem_filter.mp hk).2)
      intro k _ _
      exact mul_nonneg hU (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
    _ = _ := by rw [mul_sum]

/-- One centered affine incidence row is bounded by its progression mass and its exact negative mean. -/
theorem abs_centered_affine_row_le (p a d Y : ℕ) (z f : ℕ → ℝ)
    {V : ℝ} (hV : 0 ≤ V) (hz : ∀ k ∈ Icc 1 Y, |z k| ≤ V) :
    |∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * z k * f k *
      ((if a * k ≡ d [MOD p] then (1 : ℝ) else 0) - 1 / p)| ≤
      V * ((∑ k ∈ (Icc 1 Y).filter (fun k => a * k ≡ d [MOD p]),
        (vonMangoldt k / (k : ℝ)) * |f k|) +
        (∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * |f k|) / p) := by
  have hmean : 0 ≤ 1 / (p : ℝ) := by positivity
  calc
    _ ≤ ∑ k ∈ Icc 1 Y, |(vonMangoldt k / (k : ℝ)) * z k * f k *
        ((if a * k ≡ d [MOD p] then (1 : ℝ) else 0) - 1 / p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * V * |f k| *
        ((if a * k ≡ d [MOD p] then (1 : ℝ) else 0) + 1 / p) := by
      apply sum_le_sum
      intro k hk
      have hMangoldt : 0 ≤ vonMangoldt k / (k : ℝ) :=
        div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k)
      have hi : 0 ≤ (if a * k ≡ d [MOD p] then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      have hind : |(if a * k ≡ d [MOD p] then (1 : ℝ) else 0) - 1 / p| ≤
          (if a * k ≡ d [MOD p] then (1 : ℝ) else 0) + 1 / p := by
        simpa only [abs_of_nonneg hi, abs_of_nonneg hmean] using
          abs_sub (if a * k ≡ d [MOD p] then (1 : ℝ) else 0) (1 / p)
      simp only [abs_mul, abs_of_nonneg hMangoldt]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hz k hk) hMangoldt) (abs_nonneg _))
        hind (abs_nonneg _) (mul_nonneg (mul_nonneg hMangoldt hV) (abs_nonneg _))
    _ = _ := by
      rw [sum_filter, sum_div, ← sum_add_distrib, mul_sum]
      apply sum_congr rfl
      intro k _
      split_ifs <;> ring

/-- Supported centered affine rows keep the reciprocal-prime gain, including all prime powers. -/
theorem exists_affine_short_row_bound :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X Y B a : ℕ,
      p.Prime → p₀ ≤ p → p ^ 2 ≤ H →
      ∀ (b : ℕ → ℕ), (∀ h ∈ Icc 1 B, p.Coprime (b h)) →
      ∀ (z f : ℕ → ℕ → ℝ) (U V W : ℝ), 0 ≤ U → 0 ≤ V → 0 ≤ W →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |z k h| ≤ V) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |f k h| ≤ U) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, f k h ≠ 0 → k ∈ Icc H X) →
      (H ≤ X → Real.log X - Real.log H + mertensWindowConstant + 1 ≤ W) →
      |∑ h ∈ Icc 1 B, ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * z k h * f k h *
        ((if a * k ≡ b h [MOD p] then (1 : ℝ) else 0) - 1 / p)| ≤
        (B : ℝ) * V * U * (1027 * W / p + 576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hprime⟩ := exists_weighted_affine_mangoldt_upper_unit_target
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X Y B a hp hpp hpH b hb z f U V W hU hV hW hz hf hsupp hwidth
  have hH : 1 ≤ H := (Nat.one_le_pow 2 p hp.pos).trans hpH
  by_cases hHX : H ≤ X
  · have hlog : 1 + Real.log X - Real.log H ≤ W := by
      have hw := hwidth hHX
      linarith only [hw, mertensWindowConstant_nonneg]
    have hterm (h : ℕ) (hh : h ∈ Icc 1 B) :
        |∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * z k h * f k h *
          ((if a * k ≡ b h [MOD p] then (1 : ℝ) else 0) - 1 / p)| ≤
          V * U * (1027 * W / p + 576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
      have hselected := (affine_supported_weight_le p a (b h) H X Y
        (fun k => f k h) hU (fun k hk => hf k hk h hh) (fun k hk => hsupp k hk h hh)).trans
          (mul_le_mul_of_nonneg_left (hprime p H X a (b h) hp hpp hpH hHX (hb h hh)) hU)
      have hselected' :
          (∑ k ∈ (Icc 1 Y).filter (fun k => a * k ≡ b h [MOD p]),
            (vonMangoldt k / (k : ℝ)) * |f k h|) ≤
          U * (1026 * W / p + 576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
        refine hselected.trans (mul_le_mul_of_nonneg_left ?_ hU)
        exact add_le_add ((mul_le_mul_of_nonneg_left hlog
          (by positivity : 0 ≤ 1026 / (p : ℝ))).trans_eq (by ring)) (le_refl _)
      have htotal := (weighted_mangoldt_interval_mass hH hHX (fun k => f k h) hU
        (fun k hk => hf k hk h hh) (fun k hk => hsupp k hk h hh)).trans
          (mul_le_mul_of_nonneg_left (hwidth hHX) hU)
      exact (abs_centered_affine_row_le p a (b h) Y (fun k => z k h) (fun k => f k h)
        hV (fun k hk => hz k hk h hh)).trans
          ((mul_le_mul_of_nonneg_left (add_le_add hselected'
            (div_le_div_of_nonneg_right htotal (Nat.cast_nonneg p))) hV).trans_eq (by ring))
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans_eq ?_)
    rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    ring
  · have hsum :
        (∑ h ∈ Icc 1 B, ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * z k h * f k h *
          ((if a * k ≡ b h [MOD p] then (1 : ℝ) else 0) - 1 / p)) = 0 := by
      apply sum_eq_zero
      intro h hh
      apply sum_eq_zero
      intro k hk
      have hfzero : f k h = 0 := by
        by_contra hne
        have hm := mem_Icc.mp (hsupp k hk h hh hne)
        exact hHX (hm.1.trans hm.2)
      rw [hfzero, mul_zero, zero_mul]
    rw [hsum, abs_zero]
    positivity

#print axioms abs_centered_affine_row_le
#print axioms exists_affine_short_row_bound

/-- A coherent finite prime band preserves the short-row progression gain after summation. -/
theorem exists_affine_short_band_bound :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ (P : Finset ℕ) (H X Y B a : ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p₀ ≤ p) → (∀ p ∈ P, p ^ 2 ≤ H) →
      ∀ (b : ℕ → ℕ → ℕ), (∀ p ∈ P, ∀ h ∈ Icc 1 B, p.Coprime (b p h)) →
      ∀ (z : ℕ → ℕ → ℕ → ℝ) (f : ℕ → ℕ → ℝ) (s U V W : ℝ),
      0 ≤ U → 0 ≤ V → 0 ≤ W →
      (∀ p ∈ P, ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |z p k h| ≤ V) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |f k h| ≤ U) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, f k h ≠ 0 → k ∈ Icc H X) →
      (H ≤ X → Real.log X - Real.log H + mertensWindowConstant + 1 ≤ W) →
      |s * ∑ p ∈ P, ∑ h ∈ Icc 1 B, ∑ k ∈ Icc 1 Y,
        (vonMangoldt k / (k : ℝ)) * z p k h * f k h *
          ((if a * k ≡ b p h [MOD p] then (1 : ℝ) else 0) - 1 / p)| ≤
        |s| * (B : ℝ) * V * U *
          (1027 * W * (∑ p ∈ P, 1 / (p : ℝ)) +
            576 * (P.card : ℝ) * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hrow⟩ := exists_affine_short_row_bound
  refine ⟨p₀, hp₀, ?_⟩
  intro P H X Y B a hp hpp hpH b hb z f s U V W hU hV hW hz hf hsupp hwidth
  rw [abs_mul]
  have hsum := (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hpP =>
    hrow p H X Y B a (hp p hpP) (hpp p hpP) (hpH p hpP)
      (b p) (hb p hpP) (z p) f U V W hU hV hW (hz p hpP) hf hsupp hwidth)
  refine (mul_le_mul_of_nonneg_left hsum (abs_nonneg s)).trans_eq ?_
  have he (p : ℕ) :
      (B : ℝ) * V * U * (1027 * W / p + 576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) =
      ((B : ℝ) * V * U) * (1027 * W * (1 / (p : ℝ)) +
        576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by ring
  simp_rw [he]
  rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
  ring

#print axioms exists_affine_short_band_bound

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
