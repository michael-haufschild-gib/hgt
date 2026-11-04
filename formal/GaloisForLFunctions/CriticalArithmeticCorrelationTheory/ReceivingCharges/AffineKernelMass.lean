import GaloisForLFunctions.BezoutValuationIncidence.Sieve.OffsetCollisionMass
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.MangoldtIntervalMass

/-!
# Reciprocal Mangoldt mass in affine kernel rows

Unit restrictions preserve supported interval mass. Prime-progression collision bounds
retain the full proper-power remainder, including empty support intervals.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open Finset ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- Unit restriction preserves the logarithmic mass of a supported positive offset family. -/
theorem unit_mangoldt_kernel_mass {H X Y B p : ℕ} (hH : 1 ≤ H)
    (f : ℕ → ℕ → ℝ) {U W : ℝ} (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hf0 : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, 0 ≤ f k h)
    (hf : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |f k h| ≤ U)
    (hsupp : ∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, f k h ≠ 0 → k ∈ Icc H X)
    (hwidth : H ≤ X → Real.log X - Real.log H + mertensWindowConstant + 1 ≤ W) :
    (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B, unitMangoldtWeight p i.1 * f i.1 i.2) ≤
      (B : ℝ) * U * W := by
  calc
    _ ≤ ∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * ∑ h ∈ Icc 1 B, f k h := by
      rw [sum_product]
      apply sum_le_sum
      intro k hk
      rw [mul_sum]
      exact sum_le_sum fun h hh => mul_le_mul_of_nonneg_right
        (unitMangoldtWeight_le p k) (hf0 k hk h hh)
    _ ≤ |∑ k ∈ Icc 1 Y, (vonMangoldt k / (k : ℝ)) * ∑ h ∈ Icc 1 B, f k h| := le_abs_self _
    _ ≤ _ := double_mangoldt_supported_sum_le hH f hU hW hf hsupp hwidth

/-- Every inverse-residue collision row of a supported offset family has the full Mangoldt bound. -/
theorem exists_unit_mangoldt_collision_row_le :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X Y B : ℕ,
      p.Prime → p₀ ≤ p → p ^ 2 ≤ H →
      ∀ (b : ℕ → ℕ), (∀ h ∈ Icc 1 B, p.Coprime (b h)) →
      ∀ (f : ℕ → ℕ → ℝ) (U W : ℝ), 0 ≤ U → 0 ≤ W →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, |f k h| ≤ U) →
      (∀ k ∈ Icc 1 Y, ∀ h ∈ Icc 1 B, f k h ≠ 0 → k ∈ Icc H X) →
      (H ≤ X → Real.log X - Real.log H + mertensWindowConstant + 1 ≤ W) →
      ∀ l j : ℕ, j ∈ Icc 1 B →
      (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
        if multiplierResidue p i.1 (b i.2) ≡ multiplierResidue p l (b j) [MOD p]
        then unitMangoldtWeight p i.1 * f i.1 i.2 else 0) ≤
        (B : ℝ) * U * (1026 * W / p + 576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hbound⟩ := exists_offset_collision_mass_upper
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X Y B hp hpp hpH b hb f U W hU hW hf hsupp hwidth l j hj
  by_cases hHX : H ≤ X
  · have he :
        (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
          if multiplierResidue p i.1 (b i.2) ≡ multiplierResidue p l (b j) [MOD p]
          then unitMangoldtWeight p i.1 * f i.1 i.2 else 0) =
        ∑ h ∈ Icc 1 B, ∑ k ∈ (Icc 1 Y).filter (fun k => p.Coprime k ∧
          multiplierResidue p k (b h) ≡ multiplierResidue p l (b j) [MOD p]),
          (vonMangoldt k / (k : ℝ)) * f k h := by
      rw [sum_product, sum_comm]
      apply sum_congr rfl
      intro h _
      exact unitMangoldtWeight_collision_sum p Y l (b h) (b j) (fun k => f k h)
    rw [he]
    have h := hbound p H X Y l hp hpp hpH hHX (Icc 1 B) b hb j hj f U hU hf hsupp
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg B) hU))
    have hlog : 1 + Real.log X - Real.log H ≤ W := by
      have hw := hwidth hHX
      linarith only [hw, mertensWindowConstant_nonneg]
    exact add_le_add ((mul_le_mul_of_nonneg_left hlog
      (by positivity : 0 ≤ 1026 / (p : ℝ))).trans_eq (by ring)) (le_refl _)
  · have hfzero (k : ℕ) (hk : k ∈ Icc 1 Y) (h : ℕ) (hh : h ∈ Icc 1 B) : f k h = 0 := by
      by_contra hne
      have hm := mem_Icc.mp (hsupp k hk h hh hne)
      exact hHX (hm.1.trans hm.2)
    have hsum :
        (∑ i ∈ Icc 1 Y ×ˢ Icc 1 B,
          if multiplierResidue p i.1 (b i.2) ≡ multiplierResidue p l (b j) [MOD p]
          then unitMangoldtWeight p i.1 * f i.1 i.2 else 0) = 0 := by
      apply sum_eq_zero
      intro i hi
      rw [hfzero i.1 (mem_product.mp hi).1 i.2 (mem_product.mp hi).2, mul_zero]
      split_ifs <;> rfl
    rw [hsum]
    positivity

#print axioms unit_mangoldt_kernel_mass
#print axioms exists_unit_mangoldt_collision_row_le

/-- The complete finite index mass costs only prime count, offset width and a logarithmic multiplier sum. -/
theorem unit_mangoldt_weight_sum_le (P : Finset ℕ) (Y B : ℕ) :
    (∑ i ∈ P ×ˢ (Icc 1 Y ×ˢ Icc 1 B), |unitMangoldtWeight i.1 i.2.1|) ≤
      (P.card : ℝ) * B * (Real.log Y + mertensWindowConstant + 1) := by
  have hW : 0 ≤ Real.log Y + mertensWindowConstant + 1 :=
    add_nonneg (add_nonneg (Real.log_natCast_nonneg Y) mertensWindowConstant_nonneg) zero_le_one
  rw [sum_product]
  calc
    _ = ∑ p ∈ P, ∑ i ∈ Icc 1 Y ×ˢ Icc 1 B, unitMangoldtWeight p i.1 := by
      apply sum_congr rfl
      intro p _
      exact sum_congr rfl fun i _ => abs_of_nonneg (unitMangoldtWeight_nonneg p i.1)
    _ ≤ ∑ p ∈ P, (B : ℝ) * 1 * (Real.log Y + mertensWindowConstant + 1) := by
      apply sum_le_sum
      intro p _
      simpa only [mul_one] using unit_mangoldt_kernel_mass
        (H := 1) (X := Y) (Y := Y) (B := B) (p := p) le_rfl (fun _ _ => (1 : ℝ))
        zero_le_one hW (fun _ _ _ _ => zero_le_one) (fun _ _ _ _ => by norm_num)
        (fun k hk _ _ _ => hk)
        (fun _ => by simp only [Nat.cast_one, Real.log_one, sub_zero, le_refl])
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

#print axioms unit_mangoldt_weight_sum_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
