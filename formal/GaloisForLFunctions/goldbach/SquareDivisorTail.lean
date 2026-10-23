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
    exact mem_Icc.mpr ⟨(Nat.succ_le_succ (Nat.zero_le (R / g))).trans ha, hb⟩
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
  calc
    _ ≤ 4 / (R : ℝ) + 4 / (R : ℝ) := add_le_add hlow hhigh
    _ = _ := by ring

private theorem gcd_sq_le_common_divisor_sum (X a b : ℕ) (ha : 1 ≤ a) (haX : a ≤ X) :
    (Nat.gcd a b : ℝ) ^ 2 ≤
      ∑ g ∈ Icc 1 X, if g ∣ a ∧ g ∣ b then (g : ℝ) ^ 2 else 0 := by
  have hgpos : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hgX : Nat.gcd a b ≤ X :=
    (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)).trans haX
  have hmem : Nat.gcd a b ∈ Icc 1 X := mem_Icc.mpr ⟨hgpos, hgX⟩
  have hle := single_le_sum
    (f := fun g : ℕ => if g ∣ a ∧ g ∣ b then (g : ℝ) ^ 2 else 0)
    (fun g _ => by split_ifs <;> positivity) hmem
  have hgd : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b :=
    ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩
  simpa only [if_pos hgd] using hle

private theorem square_tail_gcd_kernel_le (R X : ℕ) (hR : 1 ≤ R) :
    (∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X,
      (Nat.gcd a b : ℝ) ^ 2 / ((a : ℝ) ^ 2 * (b : ℝ) ^ 2)) ≤ 8 / R := by
  have hpoint : ∀ a ∈ Icc (R + 1) X, ∀ b ∈ Icc (R + 1) X,
      (Nat.gcd a b : ℝ) ^ 2 / ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) ≤
        ∑ g ∈ Icc 1 X, (g : ℝ) ^ 2 *
          (if g ∣ a then 1 / (a : ℝ) ^ 2 else 0) *
          (if g ∣ b then 1 / (b : ℝ) ^ 2 else 0) := by
    intro a ha b _
    obtain ⟨haR, haX⟩ := mem_Icc.mp ha
    calc
      _ ≤ (∑ g ∈ Icc 1 X, if g ∣ a ∧ g ∣ b then (g : ℝ) ^ 2 else 0) /
          ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right
          (gcd_sq_le_common_divisor_sum X a b (by omega) haX) (by positivity)
      _ = _ := by
        rw [sum_div]
        refine sum_congr rfl fun g _ => ?_
        by_cases hga : g ∣ a <;> by_cases hgb : g ∣ b <;>
          simp only [hga, hgb, and_self, and_false, false_and, if_true, if_false,
            mul_zero, zero_mul, zero_div] <;> ring
  refine (sum_le_sum fun a ha => sum_le_sum fun b hb => hpoint a ha b hb).trans ?_
  have hswap :
      (∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X,
        ∑ g ∈ Icc 1 X, (g : ℝ) ^ 2 *
          (if g ∣ a then 1 / (a : ℝ) ^ 2 else 0) *
          (if g ∣ b then 1 / (b : ℝ) ^ 2 else 0)) =
      ∑ g ∈ Icc 1 X, (g : ℝ) ^ 2 *
        (∑ d ∈ (Icc (R + 1) X).filter (g ∣ ·), (1 : ℝ) / (d : ℝ) ^ 2) ^ 2 := by
    calc
      _ = ∑ g ∈ Icc 1 X, ∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X,
            (g : ℝ) ^ 2 * (if g ∣ a then 1 / (a : ℝ) ^ 2 else 0) *
              (if g ∣ b then 1 / (b : ℝ) ^ 2 else 0) := by
        rw [sum_congr rfl (fun a (_ : a ∈ Icc (R + 1) X) => sum_comm)]
        exact sum_comm
      _ = _ := by
        refine sum_congr rfl fun g _ => ?_
        rw [sum_filter]
        simp only [pow_two]
        rw [sum_mul_sum, mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        exact sum_congr rfl fun b _ => by ring
  rw [hswap]
  exact sum_common_square_divisor_majorant_le R X hR

private theorem square_divisor_window_second_moment_le (R X : ℕ) :
    (∑ n ∈ Icc 1 X,
      (((Icc (R + 1) X).filter (fun d => d ^ 2 ∣ n)).card : ℝ) ^ 2) ≤
      (X : ℝ) * ∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X,
        (Nat.gcd a b : ℝ) ^ 2 / ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) := by
  have hexpand : ∀ n : ℕ,
      (((Icc (R + 1) X).filter (fun d => d ^ 2 ∣ n)).card : ℝ) ^ 2 =
        ∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X,
          if a ^ 2 ∣ n ∧ b ^ 2 ∣ n then (1 : ℝ) else 0 := by
    intro n
    have hcard : (((Icc (R + 1) X).filter (fun d => d ^ 2 ∣ n)).card : ℝ) =
        ∑ d ∈ Icc (R + 1) X, if d ^ 2 ∣ n then (1 : ℝ) else 0 := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    rw [sq, hcard, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    by_cases ha : a ^ 2 ∣ n <;> by_cases hb : b ^ 2 ∣ n <;> simp [ha, hb]
  rw [sum_congr rfl fun n _ => hexpand n]
  have hswap :
      (∑ n ∈ Icc 1 X, ∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X,
        if a ^ 2 ∣ n ∧ b ^ 2 ∣ n then (1 : ℝ) else 0) =
      ∑ a ∈ Icc (R + 1) X, ∑ b ∈ Icc (R + 1) X, ∑ n ∈ Icc 1 X,
        if a ^ 2 ∣ n ∧ b ^ 2 ∣ n then (1 : ℝ) else 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ => sum_comm
  rw [hswap, mul_sum]
  refine sum_le_sum fun a ha => ?_
  rw [mul_sum]
  refine sum_le_sum fun b hb => ?_
  have ha1 : 1 ≤ a := by have := (mem_Icc.mp ha).1; omega
  have hb1 : 1 ≤ b := by have := (mem_Icc.mp hb).1; omega
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hcount := RHTower.Sieve.card_filter_dvd_pair_le X
    (a := a ^ 2) (b := b ^ 2) (one_le_pow₀ ha1) (one_le_pow₀ hb1)
  simp only [Nat.pow_gcd_pow, Nat.cast_pow] at hcount
  exact hcount.trans_eq (by ring)

/-- Number of omitted square divisors, counted by their positive bases. -/
def squareDivisorTail (R n : ℕ) : ℕ :=
  ((Icc (R + 1) n).filter (fun d => d ^ 2 ∣ n)).card

/-- A uniform second-moment bound for the squarefreeness truncation error. -/
theorem sum_squareDivisorTail_sq_le (R : ℕ+) (X : ℕ) :
    (∑ n ∈ Icc 1 X, (squareDivisorTail R n : ℝ) ^ 2) ≤
      8 * (X : ℝ) / (R : ℕ) := by
  have hcap : ∀ n ∈ Icc 1 X, (squareDivisorTail R n : ℝ) ^ 2 ≤
      (((Icc ((R : ℕ) + 1) X).filter (fun d => d ^ 2 ∣ n)).card : ℝ) ^ 2 := by
    intro n hn
    have hsub : (Icc ((R : ℕ) + 1) n).filter (fun d => d ^ 2 ∣ n) ⊆
        (Icc ((R : ℕ) + 1) X).filter (fun d => d ^ 2 ∣ n) :=
      filter_subset_filter _ (Icc_subset_Icc_right (mem_Icc.mp hn).2)
    have hcast : (squareDivisorTail R n : ℝ) ≤
        (((Icc ((R : ℕ) + 1) X).filter (fun d => d ^ 2 ∣ n)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcast 2
  calc
    _ ≤ ∑ n ∈ Icc 1 X,
        (((Icc ((R : ℕ) + 1) X).filter (fun d => d ^ 2 ∣ n)).card : ℝ) ^ 2 :=
      sum_le_sum hcap
    _ ≤ (X : ℝ) * ∑ a ∈ Icc ((R : ℕ) + 1) X, ∑ b ∈ Icc ((R : ℕ) + 1) X,
        (Nat.gcd a b : ℝ) ^ 2 / ((a : ℝ) ^ 2 * (b : ℝ) ^ 2) :=
      square_divisor_window_second_moment_le R X
    _ ≤ (X : ℝ) * (8 / (R : ℕ)) :=
      mul_le_mul_of_nonneg_left (square_tail_gcd_kernel_le R X R.pos) (Nat.cast_nonneg X)
    _ = _ := by ring

end GaloisForLFunctions.Goldbach
