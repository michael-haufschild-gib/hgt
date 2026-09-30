import GaloisForLFunctions.RHTower.SteinhausSmoothRoughSum
import GaloisForLFunctions.RHTower.SteinhausEulerRoughCount

open scoped BigOperators

noncomputable section
namespace RHTower
open SteinhausModel

/-- The literal rough count at an integer quotient counts the finite multiplication constraint. -/
theorem roughCount_nat_div_eq_card_mul_le (P : Finset ℕ) (N d : ℕ) (hd : 0 < d) :
    roughCount P ((N : ℝ) / d) =
      (((Finset.Icc 1 N).filter (fun b => ∀ p ∈ P, ¬p ∣ b)).filter
        (fun b => b * d ≤ N)).card := by
  classical
  unfold roughCount
  rw [Nat.floor_div_eq_div]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hb1, hbd⟩, hr⟩
    have hprod := (Nat.le_div_iff_mul_le hd).mp hbd
    have hbd' : b ≤ b * d := by simpa using Nat.mul_le_mul_left b hd
    have hbN : b ≤ N := hbd'.trans hprod
    exact ⟨⟨⟨hb1, hbN⟩, hr⟩, hprod⟩
  · rintro ⟨⟨⟨hb1, _⟩, hr⟩, hprod⟩
    exact ⟨⟨hb1, (Nat.le_div_iff_mul_le hd).mpr hprod⟩, hr⟩

/-- A pair scale beyond the arithmetic cutoff has exactly zero rough count. -/
theorem roughCount_nat_div_eq_zero_of_lt (P : Finset ℕ) {N d : ℕ} (h : N < d) :
    roughCount P ((N : ℝ) / d) = 0 := by
  simp [roughCount, Nat.floor_div_eq_div, Nat.div_eq_of_lt h]

private theorem sum_rough_pair_indicator (P : Finset ℕ) (N a c : ℕ)
    (ha : 0 < a) (z : ℂ) :
    (∑ b ∈ (Finset.Icc 1 N).filter (fun b => ∀ p ∈ P, ¬p ∣ b),
      if a * b ≤ N ∧ c * b ≤ N then z else 0) =
      (roughCount P ((N : ℝ) / (max a c : ℕ)) : ℂ) * z := by
  classical
  have htest (b : ℕ) : (a * b ≤ N ∧ c * b ≤ N) ↔ b * max a c ≤ N := by
    rcases le_total a c with hac | hca
    · have hab := Nat.mul_le_mul_right b hac
      rw [max_eq_right hac, Nat.mul_comm b]
      omega
    · have hcb := Nat.mul_le_mul_right b hca
      rw [max_eq_left hca, Nat.mul_comm b]
      omega
  simp_rw [htest]
  rw [← Finset.sum_filter]
  rw [roughCount_nat_div_eq_card_mul_le P N (max a c) (ha.trans_le (le_max_left _ _))]
  simp

private theorem sum_rough_normSq_eq_pairCount (P A : Finset ℕ) (N : ℕ)
    (F : ℕ → ℂ) (hA : ∀ a ∈ A, 0 < a) :
    ((∑ b ∈ (Finset.Icc 1 N).filter (fun b => ∀ p ∈ P, ¬p ∣ b),
      ‖∑ a ∈ A, if a * b ≤ N then F a else 0‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ∑ a ∈ A, ∑ c ∈ A,
        (roughCount P ((N : ℝ) / (max a c : ℕ)) : ℂ) *
          (F a * (starRingEnd ℂ) (F c)) := by
  classical
  let R := (Finset.Icc 1 N).filter (fun b => ∀ p ∈ P, ¬p ∣ b)
  have hsquare (b : ℕ) :
      ((‖∑ a ∈ A, if a * b ≤ N then F a else 0‖ ^ (2 : ℕ) : ℝ) : ℂ) =
        ∑ a ∈ A, ∑ c ∈ A,
          if a * b ≤ N ∧ c * b ≤ N then F a * (starRingEnd ℂ) (F c) else 0 := by
    have hsq (z : ℂ) : ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [hsq, map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hab : a * b ≤ N <;> by_cases hcb : c * b ≤ N <;> simp [hab, hcb]
  calc
    _ = ∑ b ∈ R, ((‖∑ a ∈ A, if a * b ≤ N then F a else 0‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = ∑ b ∈ R, ∑ a ∈ A, ∑ c ∈ A,
        if a * b ≤ N ∧ c * b ≤ N then F a * (starRingEnd ℂ) (F c) else 0 :=
      Finset.sum_congr rfl (fun b _ => hsquare b)
    _ = ∑ a ∈ A, ∑ c ∈ A, ∑ b ∈ R,
        if a * b ≤ N ∧ c * b ≤ N then F a * (starRingEnd ℂ) (F c) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro c hc
      exact sum_rough_pair_indicator P N a c (hA a ha) _

/-- Every coefficient of the literal frozen-prefix variance is the actual finite rough count. -/
theorem integral_normSq_steinhausSummatory_frozenPrefix_eq_pairCount
    (y N : ℕ) (ω : Omega) :
    ((∫ η, ‖∑ n ∈ Finset.Icc 1 N,
      X n (freezeSteinhausPrefix (Nat.primesBelow y) ω η)‖ ^ (2 : ℕ)
        ∂steinhausMeasure : ℝ) : ℂ) =
      ∑ a ∈ Nat.smoothNumbersUpTo N y, ∑ c ∈ Nat.smoothNumbersUpTo N y,
        (roughCount (Nat.primesBelow y) ((N : ℝ) / (max a c : ℕ)) : ℂ) *
          (X a ω * (starRingEnd ℂ) (X c ω)) := by
  rw [integral_normSq_steinhausSummatory_frozenPrefix_eq_rough]
  exact sum_rough_normSq_eq_pairCount _ _ _ (fun a => X a ω)
    (fun a ha => Nat.pos_of_ne_zero
      (Nat.ne_zero_of_mem_smoothNumbers (Nat.mem_smoothNumbersUpTo.mp ha).2))

end RHTower
