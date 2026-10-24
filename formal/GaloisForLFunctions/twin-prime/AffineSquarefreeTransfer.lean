import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.PNat.Basic

/-!
# Squarefree projection on primitive affine rows

Truncating the square-divisor expansion of Möbius gives an explicit error on
each primitive affine progression. Two different truncation lengths control
the product error without assuming cancellation of either arithmetic row.
-/

namespace TwinPrime.AffineSquarefree

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- A positive affine progression with reduced, coprime slope and intercept. -/
structure Row where
  slope : ℕ+
  intercept : Fin (slope : ℕ)
  primitive : Nat.Coprime (slope : ℕ) (intercept : ℕ)

def Row.eval (F : Row) (t : ℕ) : ℕ := (F.slope : ℕ) * t + F.intercept

theorem Row.eval_pos (F : Row) (t : ℕ+) : 0 < F.eval t :=
  Nat.add_pos_left (Nat.mul_pos F.slope.pos t.pos) _

theorem Row.eval_mono (F : Row) : Monotone F.eval := by
  intro s t h
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

/-- The square-divisor truncation of the Liouville projection. -/
def approx (R n : ℕ) : ℝ :=
  (liouville n : ℝ) * ∑ d ∈ (Icc 1 R).filter (fun d => d * d ∣ n), (μ d : ℝ)

private theorem abs_moebius_le_one (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  rcases moebius_eq_or n with h | h | h <;> simp [h]

private theorem abs_liouville_eq_one (n : ℕ+) : |(liouville n : ℝ)| = 1 := by
  simp [liouville_apply n.ne_zero, abs_pow]

private theorem moebius_eq_liouville_mul_sq (n : ℕ) :
    (μ n : ℝ) = (liouville n : ℝ) * (μ n : ℝ) ^ 2 := by
  by_cases hn : Squarefree n
  · have heq : (liouville n : ℝ) = (μ n : ℝ) := by
      simp only [liouville_apply hn.ne_zero, moebius_apply_of_squarefree hn]
    rw [heq]
    rcases moebius_eq_or n with h | h | h <;> simp [h]
  · simp [moebius_eq_zero_of_not_squarefree hn]

/-- Every square divisor of a positive integer lies below its integer square root. -/
private theorem square_divisor_le_sqrt (n : ℕ+) {d : ℕ} (hd : d * d ∣ (n : ℕ)) :
    d ≤ Nat.sqrt n := by
  exact Nat.le_sqrt.mpr (Nat.le_of_dvd n.pos hd)

private theorem squareDivisors_filter (n : ℕ+) (R : ℕ) :
    (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)) =
      ((Icc 1 (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ))).filter
        (fun d => d ≤ R) := by
  ext d
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hd, hR⟩, hdiv⟩
    exact ⟨⟨⟨hd, square_divisor_le_sqrt n hdiv⟩, hdiv⟩, hR⟩
  · rintro ⟨⟨⟨hd, _⟩, hdiv⟩, hR⟩
    exact ⟨⟨hd, hR⟩, hdiv⟩

private theorem squareDivisors_sum (n : ℕ+) :
    ∑ d ∈ (Icc 1 (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)),
      (μ d : ℝ) = (μ n : ℝ) ^ 2 := by
  have heq : (Icc 1 (n : ℕ)).filter (fun d => d * d ∣ (n : ℕ)) =
      (Icc 1 (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)) := by
    ext d
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨hd, _⟩, hdiv⟩
      exact ⟨⟨hd, square_divisor_le_sqrt n hdiv⟩, hdiv⟩
    · rintro ⟨⟨hd, hs⟩, hdiv⟩
      exact ⟨⟨hd, hs.trans (Nat.sqrt_le_self _)⟩, hdiv⟩
  have h := RHTower.sum_moebius_sq_dvd_Icc (n := n) n.pos
  rw [heq] at h
  exact_mod_cast h

/-- The projection error is exactly the omitted signed square-divisor tail. -/
theorem moebius_sub_approx (n : ℕ+) (R : ℕ) :
    (μ n : ℝ) - approx R n = (liouville n : ℝ) *
      ∑ d ∈ (Icc (R + 1) (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)),
        (μ d : ℝ) := by
  have htail :
      ((Icc 1 (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ))).filter
          (fun d => ¬ d ≤ R) =
        (Icc (R + 1) (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)) := by
    ext d
    simp only [mem_filter, mem_Icc]
    omega
  have hsum :
      (∑ d ∈ (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)), (μ d : ℝ)) +
        (∑ d ∈ (Icc (R + 1) (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)),
          (μ d : ℝ)) = (μ n : ℝ) ^ 2 := by
    rw [squareDivisors_filter n R, ← htail, sum_filter_add_sum_filter_not,
      squareDivisors_sum]
  rw [approx, moebius_eq_liouville_mul_sq n, ← hsum]
  ring

/-- A truncated projection has size at most the number of retained indices. -/
theorem abs_approx_le (n : ℕ+) (R : ℕ) : |approx R n| ≤ (R : ℝ) := by
  rw [approx, abs_mul, abs_liouville_eq_one, one_mul]
  calc
    |∑ d ∈ (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)), (μ d : ℝ)|
        ≤ ∑ d ∈ (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)), |(μ d : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)), (1 : ℝ) :=
      sum_le_sum fun d _ => abs_moebius_le_one d
    _ ≤ ∑ _d ∈ Icc 1 R, (1 : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
    _ = (R : ℝ) := by simp

/-- Pointwise projection error is bounded by the number of omitted square divisors. -/
theorem abs_moebius_sub_approx_le (n : ℕ+) (R : ℕ) :
    |(μ n : ℝ) - approx R n| ≤
      (((Icc (R + 1) (Nat.sqrt n)).filter
        (fun d => d * d ∣ (n : ℕ))).card : ℝ) := by
  rw [moebius_sub_approx, abs_mul, abs_liouville_eq_one, one_mul]
  calc
    |∑ d ∈ (Icc (R + 1) (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)),
        (μ d : ℝ)| ≤
        ∑ d ∈ (Icc (R + 1) (Nat.sqrt n)).filter (fun d => d * d ∣ (n : ℕ)),
          |(μ d : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (Icc (R + 1) (Nat.sqrt n)).filter
        (fun d => d * d ∣ (n : ℕ)), (1 : ℝ) :=
      sum_le_sum fun d _ => abs_moebius_le_one d
    _ = _ := by simp

/-- Divisibility of a primitive affine row selects at most one residue class. -/
theorem Row.modEq_of_dvd (F : Row) (q : ℕ) {s t : ℕ}
    (hs : q ∣ F.eval s) (ht : q ∣ F.eval t) : Nat.ModEq q s t := by
  have hc : Nat.Coprime (F.slope : ℕ) (F.eval s) :=
    (Nat.coprime_mul_left_add_right _ _ _).mpr F.primitive
  have hq : Nat.Coprime q (F.slope : ℕ) :=
    (Nat.Coprime.of_dvd_right hs hc).symm
  have he : Nat.ModEq q (F.eval s) (F.eval t) := by
    change F.eval s % q = F.eval t % q
    rw [Nat.mod_eq_zero_of_dvd hs, Nat.mod_eq_zero_of_dvd ht]
  have hm : Nat.ModEq q ((F.slope : ℕ) * s) ((F.slope : ℕ) * t) :=
    Nat.ModEq.add_right_cancel (show Nat.ModEq q (F.intercept : ℕ) F.intercept from rfl) he
  exact Nat.ModEq.cancel_left_of_coprime hq hm

/-- Quotient and residue determine each selected index, giving the interval count. -/
theorem Row.card_dvd_le (F : Row) (T : ℕ) (q : ℕ+) :
    ((Icc 1 T).filter (fun t => (q : ℕ) ∣ F.eval t)).card ≤ T / q + 1 := by
  have hcount := card_le_card_of_injOn (s := (Icc 1 T).filter
      (fun t => (q : ℕ) ∣ F.eval t)) (t := range (T / q + 1))
      (fun t => t / (q : ℕ))
      (by
        intro t ht
        exact mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp ht).1).2)))
      (by
        intro s hs t ht he
        have hm := F.modEq_of_dvd q (mem_filter.mp hs).2 (mem_filter.mp ht).2
        change s % (q : ℕ) = t % (q : ℕ) at hm
        change s / (q : ℕ) = t / (q : ℕ) at he
        have h₁ := Nat.mod_add_div s (q : ℕ)
        have h₂ := Nat.mod_add_div t (q : ℕ)
        rw [he, hm] at h₁
        exact h₁.symm.trans h₂)
  simpa only [card_range] using hcount

theorem Row.card_dvd_le_real (F : Row) (T : ℕ) (q : ℕ+) :
    (((Icc 1 T).filter (fun t => (q : ℕ) ∣ F.eval t)).card : ℝ) ≤
      (T : ℝ) / (q : ℕ) + 1 := by
  calc
    _ ≤ ((T / (q : ℕ) + 1 : ℕ) : ℝ) := by exact_mod_cast F.card_dvd_le T q
    _ ≤ (T : ℝ) / (q : ℕ) + 1 := by
      push_cast
      have hd : ((T / (q : ℕ) : ℕ) : ℝ) ≤ (T : ℝ) / (q : ℕ) := Nat.cast_div_le
      exact add_le_add hd (le_refl (1 : ℝ))

/-- Summed squarefree-projection error on an entire primitive affine row. -/
theorem sum_abs_moebius_sub_approx_le (F : Row) (T : ℕ) (R : ℕ+) :
    ∑ t ∈ Icc 1 T, |(μ (F.eval t) : ℝ) - approx R (F.eval t)| ≤
      (T : ℝ) / (R : ℕ) + (Nat.sqrt (F.eval T) : ℝ) := by
  have hpoint : ∀ t ∈ Icc 1 T,
      |(μ (F.eval t) : ℝ) - approx R (F.eval t)| ≤
        ∑ d ∈ Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T)),
          if d * d ∣ F.eval t then (1 : ℝ) else 0 := by
    intro t ht
    have htpos : 0 < t := (mem_Icc.mp ht).1
    have hp := abs_moebius_sub_approx_le ⟨F.eval t, F.eval_pos ⟨t, htpos⟩⟩ (R : ℕ)
    have hsub :
        (Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval t))).filter (fun d => d * d ∣ F.eval t) ⊆
          (Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T))).filter
            (fun d => d * d ∣ F.eval t) := by
      intro d hd
      rcases mem_filter.mp hd with ⟨hI, hdiv⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hI).1,
        (mem_Icc.mp hI).2.trans (Nat.sqrt_le_sqrt (F.eval_mono (mem_Icc.mp ht).2))⟩,
          hdiv⟩
    calc
      _ ≤ (((Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval t))).filter
          (fun d => d * d ∣ F.eval t)).card : ℝ) := hp
      _ ≤ (((Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T))).filter
          (fun d => d * d ∣ F.eval t)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
      _ = _ := by rw [← sum_filter]; simp only [sum_const, nsmul_eq_mul, mul_one]
  have hcard : ((Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T))).card : ℝ) ≤
      (Nat.sqrt (F.eval T) : ℝ) := by
    have hs : Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T)) ⊆ Icc 1 (Nat.sqrt (F.eval T)) := by
      intro d hd
      exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hd).1; omega, (mem_Icc.mp hd).2⟩
    have hc := card_le_card hs
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      (show ((Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T))).card : ℝ) ≤
        ((Icc 1 (Nat.sqrt (F.eval T))).card : ℝ) by exact_mod_cast hc)
  calc
    _ ≤ ∑ t ∈ Icc 1 T, ∑ d ∈ Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T)),
        if d * d ∣ F.eval t then (1 : ℝ) else 0 := sum_le_sum hpoint
    _ = ∑ d ∈ Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T)),
        (((Icc 1 T).filter (fun t => d * d ∣ F.eval t)).card : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ d ∈ Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T)),
        ((T : ℝ) / (d : ℝ) ^ 2 + 1) := by
      apply sum_le_sum
      intro d hd
      have hdpos : 0 < d := by have := (mem_Icc.mp hd).1; omega
      have h := F.card_dvd_le_real T ⟨d * d, Nat.mul_pos hdpos hdpos⟩
      change (((Icc 1 T).filter (fun t => d * d ∣ F.eval t)).card : ℝ) ≤
        (T : ℝ) / ((d * d : ℕ) : ℝ) + 1 at h
      simpa only [Nat.cast_mul, pow_two] using h
    _ = (T : ℝ) *
        (∑ d ∈ Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T)), 1 / (d : ℝ) ^ 2) +
          ((Icc ((R : ℕ) + 1) (Nat.sqrt (F.eval T))).card : ℝ) := by
      rw [sum_add_distrib, mul_sum]
      simp only [mul_one_div, sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (T : ℝ) * (1 / (R : ℕ)) + (Nat.sqrt (F.eval T) : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (RHTower.sum_inv_sq_tail_le R.pos (Nat.sqrt (F.eval T))) (Nat.cast_nonneg T)) hcard
    _ = _ := by rw [mul_one_div]

/-- The actual two-Möbius correlation along two affine rows. -/
def moebiusCorrelation (F G : Row) (T : ℕ) : ℝ :=
  ∑ t ∈ Icc 1 T, (μ (F.eval t) : ℝ) * (μ (G.eval t) : ℝ)

/-- The retained two-Liouville correlations with their square-divisibility constraints. -/
def liouvilleCorrelation (F G : Row) (T R S : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 S, (μ d : ℝ) * (μ e : ℝ) *
    ∑ t ∈ (Icc 1 T).filter (fun t => d * d ∣ F.eval t ∧ e * e ∣ G.eval t),
      (liouville (F.eval t) : ℝ) * (liouville (G.eval t) : ℝ)

/-- Expanding both truncations retains the signs and the two divisibility constraints. -/
theorem sum_approx_mul_eq (F G : Row) (T R S : ℕ) :
    ∑ t ∈ Icc 1 T, approx R (F.eval t) * approx S (G.eval t) =
      liouvilleCorrelation F G T R S := by
  have hpoint (t : ℕ) : approx R (F.eval t) * approx S (G.eval t) =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc 1 S, (μ d : ℝ) * (μ e : ℝ) *
        (if d * d ∣ F.eval t ∧ e * e ∣ G.eval t then
          (liouville (F.eval t) : ℝ) * (liouville (G.eval t) : ℝ) else 0) := by
    simp only [approx, sum_filter]
    rw [mul_sum, mul_sum, sum_mul_sum]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    by_cases hd : d * d ∣ F.eval t <;> by_cases he : e * e ∣ G.eval t
    all_goals simp only [hd, he, and_self, and_true, and_false,
      if_true, if_false, mul_zero, zero_mul]
    ring
  simp_rw [hpoint]
  rw [sum_comm]
  unfold liouvilleCorrelation
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [sum_filter, mul_sum]

private theorem abs_product_error_le (n m : ℕ+) (R S : ℕ) :
    |(μ n : ℝ) * (μ m : ℝ) - approx R n * approx S m| ≤
      |(μ n : ℝ) - approx R n| + (R : ℝ) * |(μ m : ℝ) - approx S m| := by
  have he : (μ n : ℝ) * (μ m : ℝ) - approx R n * approx S m =
      ((μ n : ℝ) - approx R n) * (μ m : ℝ) +
        approx R n * ((μ m : ℝ) - approx S m) := by ring
  rw [he]
  calc
    _ ≤ |((μ n : ℝ) - approx R n) * (μ m : ℝ)| +
        |approx R n * ((μ m : ℝ) - approx S m)| := abs_add_le _ _
    _ = |(μ n : ℝ) - approx R n| * |(μ m : ℝ)| +
        |approx R n| * |(μ m : ℝ) - approx S m| := by rw [abs_mul, abs_mul]
    _ ≤ |(μ n : ℝ) - approx R n| * 1 +
        (R : ℝ) * |(μ m : ℝ) - approx S m| :=
      add_le_add (mul_le_mul_of_nonneg_left (abs_moebius_le_one m) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (abs_approx_le n R) (abs_nonneg _))
    _ = _ := by rw [mul_one]

/-- Uniform finite transfer from Möbius to square-divisor Liouville correlations. -/
theorem abs_correlation_sub_le (F G : Row) (T : ℕ) (R S : ℕ+) :
    |moebiusCorrelation F G T - liouvilleCorrelation F G T R S| ≤
      (T : ℝ) / (R : ℕ) + (Nat.sqrt (F.eval T) : ℝ) +
        (R : ℕ) * ((T : ℝ) / (S : ℕ) + (Nat.sqrt (G.eval T) : ℝ)) := by
  rw [← sum_approx_mul_eq, moebiusCorrelation, ← sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ Icc 1 T,
        |(μ (F.eval t) : ℝ) * (μ (G.eval t) : ℝ) -
          approx R (F.eval t) * approx S (G.eval t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Icc 1 T,
        (|(μ (F.eval t) : ℝ) - approx R (F.eval t)| +
          (R : ℕ) * |(μ (G.eval t) : ℝ) - approx S (G.eval t)|) := by
      apply sum_le_sum
      intro t ht
      have htpos : 0 < t := (mem_Icc.mp ht).1
      exact abs_product_error_le ⟨F.eval t, F.eval_pos ⟨t, htpos⟩⟩
        ⟨G.eval t, G.eval_pos ⟨t, htpos⟩⟩ R S
    _ = (∑ t ∈ Icc 1 T, |(μ (F.eval t) : ℝ) - approx R (F.eval t)|) +
        (R : ℕ) * ∑ t ∈ Icc 1 T, |(μ (G.eval t) : ℝ) - approx S (G.eval t)| := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ _ := add_le_add (sum_abs_moebius_sub_approx_le F T R)
      (mul_le_mul_of_nonneg_left (sum_abs_moebius_sub_approx_le G T S) (Nat.cast_nonneg _))

/-- Squaring the second cutoff pays for the first truncation's possible size. -/
theorem abs_correlation_sub_square_cutoff_le (F G : Row) (T : ℕ) (R : ℕ+) :
    |moebiusCorrelation F G T - liouvilleCorrelation F G T R (R ^ 2 : ℕ+)| ≤
      2 * (T : ℝ) / (R : ℕ) + (Nat.sqrt (F.eval T) : ℝ) +
        (R : ℕ) * (Nat.sqrt (G.eval T) : ℝ) := by
  have h := abs_correlation_sub_le F G T R (R ^ 2)
  have hR : ((R : ℕ) : ℝ) ≠ 0 := by exact_mod_cast R.ne_zero
  have he : (T : ℝ) / (R : ℕ) + (Nat.sqrt (F.eval T) : ℝ) +
      (R : ℕ) * ((T : ℝ) / ((R ^ 2 : ℕ+) : ℕ) + (Nat.sqrt (G.eval T) : ℝ)) =
        2 * (T : ℝ) / (R : ℕ) + (Nat.sqrt (F.eval T) : ℝ) +
          (R : ℕ) * (Nat.sqrt (G.eval T) : ℝ) := by
    rw [PNat.pow_coe, Nat.cast_pow]
    field_simp [hR]
    ring
  exact h.trans_eq he

end

end TwinPrime.AffineSquarefree

#print axioms TwinPrime.AffineSquarefree.moebius_sub_approx

#print axioms TwinPrime.AffineSquarefree.Row.card_dvd_le

#print axioms TwinPrime.AffineSquarefree.sum_abs_moebius_sub_approx_le

#print axioms TwinPrime.AffineSquarefree.sum_approx_mul_eq

#print axioms TwinPrime.AffineSquarefree.abs_correlation_sub_le

#print axioms TwinPrime.AffineSquarefree.abs_correlation_sub_square_cutoff_le
