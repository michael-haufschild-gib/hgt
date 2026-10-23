import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareMoment

/-!
# Mean square of the omitted square divisors

The number of square divisors with base above `R` has second moment at most
`8X/R` on `[1,X]`. This controls squarefreeness truncation against divisor
multiplicities without imposing a condition on the additive target.
-/

noncomputable section

namespace GaloisForLFunctions.Goldbach

open Finset

private theorem sum_inv_sq_prefix_le_two (X : ℕ) :
    (∑ d ∈ Icc 1 X, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 2 := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp
  have hset : Icc 1 X = insert 1 (Icc 2 X) := by
    ext d
    simp only [mem_Icc, mem_insert]
    omega
  rw [hset, sum_insert (by simp)]
  have htail := RHTower.Sieve.sum_Icc_inv_sq_le (R := 1) (by omega) X
  norm_num at htail ⊢
  linarith

private theorem sum_inv_sq_multiples (R X g : ℕ) (hg : 0 < g) :
    (∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·), (1 : ℝ) / (d : ℝ) ^ 2) =
      (1 / (g : ℝ) ^ 2) *
        ∑ a ∈ Icc (R / g + 1) (X / g), (1 : ℝ) / (a : ℝ) ^ 2 := by
  classical
  rw [mul_sum]
  refine (sum_bij' (fun a _ => g * a) (fun d _ => d / g) ?_ ?_ ?_ ?_ ?_).symm
  · intro a ha
    obtain ⟨haR, haX⟩ := mem_Icc.mp ha
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, ⟨a, rfl⟩⟩
    · have hlt : R < a * g := (Nat.div_lt_iff_lt_mul hg).mp (by omega)
      simpa [Nat.mul_comm] using hlt
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp haX
  · intro d hd
    obtain ⟨hdI, hgd⟩ := mem_filter.mp hd
    obtain ⟨hdR, hdX⟩ := mem_Icc.mp hdI
    apply mem_Icc.mpr
    refine ⟨?_, Nat.div_le_div_right hdX⟩
    have hmul : d / g * g = d := Nat.div_mul_cancel hgd
    have hlt : R / g < d / g := (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    omega
  · intro a _
    exact Nat.mul_div_cancel_left a hg
  · intro d hd
    exact Nat.mul_div_cancel' (mem_filter.mp hd).2
  · intro a _
    push_cast
    field_simp

private theorem sum_inv_sq_multiples_le (R X g : ℕ) (hg : 0 < g) :
    (∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·), (1 : ℝ) / (d : ℝ) ^ 2) ≤
      2 / (g : ℝ) ^ 2 := by
  rw [sum_inv_sq_multiples R X g hg]
  have hsub : (Icc (R / g + 1) (X / g) : Finset ℕ) ⊆ Icc 1 (X / g) := by
    intro a ha
    obtain ⟨ha, hb⟩ := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨by omega, hb⟩
  have hsum : (∑ a ∈ (Icc (R / g + 1) (X / g) : Finset ℕ),
      (1 : ℝ) / (a : ℝ) ^ 2) ≤ 2 :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (sum_inv_sq_prefix_le_two (X / g))
  calc
    _ ≤ (1 / (g : ℝ) ^ 2) * 2 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

private theorem sum_inv_sq_multiples_le_cutoff (R X g : ℕ)
    (hg : 0 < g) (hgR : g ≤ R) :
    (∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·), (1 : ℝ) / (d : ℝ) ^ 2) ≤
      2 / ((g : ℝ) * R) := by
  have hquot : 1 ≤ R / g := Nat.div_pos hgR hg
  have hquotR : (0 : ℝ) < (R / g : ℕ) := by exact_mod_cast hquot
  have hgR' : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (lt_of_lt_of_le hg hgR)
  have hnat : R ≤ 2 * g * (R / g) := by
    have hrem := Nat.mod_lt R hg
    have hdecomp := Nat.mod_add_div R g
    have hge : g ≤ g * (R / g) := Nat.le_mul_of_pos_right g hquot
    nlinarith only [hrem, hdecomp, hge]
  have hreal : (R : ℝ) ≤ 2 * g * (R / g : ℕ) := by exact_mod_cast hnat
  rw [sum_inv_sq_multiples R X g hg]
  calc
    _ ≤ (1 / (g : ℝ) ^ 2) * (1 / (R / g : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (RHTower.Sieve.sum_Icc_inv_sq_le hquot (X / g)) (by positivity)
    _ ≤ 2 / ((g : ℝ) * R) := by
      apply (le_div_iff₀ (mul_pos hgR' hR)).mpr
      field_simp
      nlinarith

private theorem sum_common_square_divisor_majorant_le (R X : ℕ) (hR : 1 ≤ R) :
    (∑ g ∈ Icc 1 X, (g : ℝ) ^ 2 *
      (∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·), (1 : ℝ) / (d : ℝ) ^ 2) ^ 2) ≤
        8 / R := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hpoint : ∀ g ∈ Icc 1 X,
      (g : ℝ) ^ 2 *
        (∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·), (1 : ℝ) / (d : ℝ) ^ 2) ^ 2 ≤
          if g ≤ R then 4 / (R : ℝ) ^ 2 else 4 / (g : ℝ) ^ 2 := by
    intro g hg
    have hgpos : 0 < g := (mem_Icc.mp hg).1
    have hgposR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have hnn : 0 ≤ ∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·),
        (1 : ℝ) / (d : ℝ) ^ 2 := sum_nonneg fun _ _ => by positivity
    by_cases hgR : g ≤ R
    · rw [if_pos hgR]
      have hb := sum_inv_sq_multiples_le_cutoff R X g hgpos hgR
      calc
        _ ≤ (g : ℝ) ^ 2 * (2 / ((g : ℝ) * R)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hb 2) (sq_nonneg _)
        _ = _ := by field_simp; ring
    · rw [if_neg hgR]
      have hb := sum_inv_sq_multiples_le R X g hgpos
      calc
        _ ≤ (g : ℝ) ^ 2 * (2 / (g : ℝ) ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn hb 2) (sq_nonneg _)
        _ = _ := by field_simp; ring
  refine (sum_le_sum hpoint).trans ?_
  have htailset : (Icc 1 X).filter (fun g : ℕ => ¬ g ≤ R) = Icc (R + 1) X := by
    ext g
    simp only [mem_filter, mem_Icc]
    omega
  have hsplit :
      (∑ g ∈ Icc 1 X, if g ≤ R then (4 : ℝ) / (R : ℝ) ^ 2 else 4 / (g : ℝ) ^ 2) =
        (∑ _g ∈ (Icc 1 X).filter (fun g : ℕ => g ≤ R), (4 : ℝ) / (R : ℝ) ^ 2) +
          ∑ g ∈ Icc (R + 1) X, (4 : ℝ) / (g : ℝ) ^ 2 := by
    rw [← htailset, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun g _ => ?_
    split_ifs <;> simp_all
  rw [hsplit]
  have hcard : (((Icc 1 X).filter (fun g : ℕ => g ≤ R)).card : ℝ) ≤ R := by
    have hsub : (Icc 1 X).filter (fun g : ℕ => g ≤ R) ⊆ Icc 1 R := by
      intro g hg
      obtain ⟨hgI, hgR⟩ := mem_filter.mp hg
      exact mem_Icc.mpr ⟨(mem_Icc.mp hgI).1, hgR⟩
    have hc := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
    exact_mod_cast hc
  have hlow :
      (∑ _g ∈ (Icc 1 X).filter (fun g : ℕ => g ≤ R), (4 : ℝ) / (R : ℝ) ^ 2) ≤
        4 / R := by
    rw [sum_const, nsmul_eq_mul]
    calc
      _ ≤ (R : ℝ) * (4 / (R : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp
  have hhigh : (∑ g ∈ Icc (R + 1) X, (4 : ℝ) / (g : ℝ) ^ 2) ≤ 4 / R := by
    calc
      _ = 4 * ∑ g ∈ Icc (R + 1) X, (1 : ℝ) / (g : ℝ) ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun _ _ => by ring
      _ ≤ 4 * (1 / (R : ℝ)) :=
        mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_Icc_inv_sq_le hR X) (by norm_num)
      _ = _ := by ring
  linarith

#check Nat.gcd_pow
#check Nat.pow_gcd_pow
#check Nat.gcd_pow_pow
#check gcd_pow
#check gcd_pow_pow
#check pow_gcd_pow
#check Nat.coprime_div_gcd_div_gcd
#check Nat.Coprime.pow

end GaloisForLFunctions.Goldbach
