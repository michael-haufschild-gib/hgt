import GaloisForLFunctions.RHTower.SquarefreeCountingAsymptotic
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.PNat.Basic

/-!
# Squarefree projection on primitive affine rows

Truncating the square-divisor expansion of Möbius gives an explicit error on
each primitive affine progression. Two different truncation lengths control
the product error without assuming cancellation of either arithmetic row.
At nonzero determinant, joint divisor incidence permits equal cutoffs: the
determinant bounds every common divisor of the two affine values.
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

/-- Two primitive affine rows with nonzero absolute determinant `D`. -/
structure Frame (D : ℕ+) where
  left : Row
  right : Row
  determinant :
    (left.slope : ℕ) * right.intercept + D = (right.slope : ℕ) * left.intercept ∨
    (right.slope : ℕ) * left.intercept + D = (left.slope : ℕ) * right.intercept

/-- The simultaneous divisor incidence count on the actual affine rows. -/
def jointDivisorCount (F G : Row) (T q r : ℕ) : ℕ :=
  ((Icc 1 T).filter (fun t => q ∣ F.eval t ∧ r ∣ G.eval t)).card

/-- A joint residue class is counted by its quotient modulo the least common multiple. -/
theorem jointDivisorCount_le_lcm (F G : Row) (T q r : ℕ) :
    jointDivisorCount F G T q r ≤ T / Nat.lcm q r + 1 := by
  have hcount := card_le_card_of_injOn
      (s := (Icc 1 T).filter (fun t => q ∣ F.eval t ∧ r ∣ G.eval t))
      (t := range (T / Nat.lcm q r + 1)) (fun t => t / Nat.lcm q r)
      (by
        intro t ht
        exact mem_range.mpr (Nat.lt_succ_of_le
          (Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp ht).1).2)))
      (by
        intro s hs t ht he
        have hq := F.modEq_of_dvd q (mem_filter.mp hs).2.1 (mem_filter.mp ht).2.1
        have hr := G.modEq_of_dvd r (mem_filter.mp hs).2.2 (mem_filter.mp ht).2.2
        have hm := Nat.mod_lcm hq hr
        change s % Nat.lcm q r = t % Nat.lcm q r at hm
        change s / Nat.lcm q r = t / Nat.lcm q r at he
        have h₁ := Nat.mod_add_div s (Nat.lcm q r)
        have h₂ := Nat.mod_add_div t (Nat.lcm q r)
        rw [he, hm] at h₁
        exact h₁.symm.trans h₂)
  simpa only [jointDivisorCount, card_range] using hcount

/-- Any common divisor of two row values divides their determinant. -/
theorem Frame.dvd_determinant {D : ℕ+} (P : Frame D) (t m : ℕ)
    (hF : m ∣ P.left.eval t) (hG : m ∣ P.right.eval t) : m ∣ (D : ℕ) := by
  have h₁ : m ∣ (P.left.slope : ℕ) * P.right.eval t := dvd_mul_of_dvd_right hG _
  have h₂ : m ∣ (P.right.slope : ℕ) * P.left.eval t := dvd_mul_of_dvd_right hF _
  rcases P.determinant with h | h
  · have he : (P.left.slope : ℕ) * P.right.eval t + D =
        (P.right.slope : ℕ) * P.left.eval t := by
      dsimp only [Row.eval]
      nlinarith only [h]
    have hd : m ∣ (P.left.slope : ℕ) * P.right.eval t + D := he.symm ▸ h₂
    exact (Nat.dvd_add_iff_right h₁).mpr hd
  · have he : (P.right.slope : ℕ) * P.left.eval t + D =
        (P.left.slope : ℕ) * P.right.eval t := by
      dsimp only [Row.eval]
      nlinarith only [h]
    have hd : m ∣ (P.right.slope : ℕ) * P.left.eval t + D := he.symm ▸ h₁
    exact (Nat.dvd_add_iff_right h₂).mpr hd

/-- The determinant bounds the density of every compatible joint divisor class. -/
theorem Frame.jointDivisorCount_le {D : ℕ+} (P : Frame D) (T : ℕ) (q r : ℕ+) :
    (jointDivisorCount P.left P.right T q r : ℝ) ≤
      (D : ℕ) * (T : ℝ) / (((q : ℕ) : ℝ) * (r : ℕ)) + 1 := by
  by_cases h : ((Icc 1 T).filter
      (fun t => (q : ℕ) ∣ P.left.eval t ∧ (r : ℕ) ∣ P.right.eval t)).Nonempty
  · obtain ⟨t, ht⟩ := h
    have hF := (mem_filter.mp ht).2.1
    have hG := (mem_filter.mp ht).2.2
    have hd : Nat.gcd (q : ℕ) (r : ℕ) ∣ (D : ℕ) :=
      P.dvd_determinant t _ ((Nat.gcd_dvd_left _ _).trans hF)
        ((Nat.gcd_dvd_right _ _).trans hG)
    have hle : (Nat.gcd (q : ℕ) (r : ℕ) : ℝ) ≤ (D : ℕ) := by
      exact_mod_cast Nat.le_of_dvd D.pos hd
    have hlpos : (0 : ℝ) < (Nat.lcm (q : ℕ) (r : ℕ) : ℝ) := by
      exact_mod_cast Nat.lcm_pos q.pos r.pos
    have hqpos : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
    have hrpos : (0 : ℝ) < ((r : ℕ) : ℝ) := by exact_mod_cast r.pos
    have hmul : (Nat.gcd (q : ℕ) (r : ℕ) : ℝ) *
        (Nat.lcm (q : ℕ) (r : ℕ) : ℝ) = ((q : ℕ) : ℝ) * (r : ℕ) := by
      exact_mod_cast Nat.gcd_mul_lcm (q : ℕ) (r : ℕ)
    have hfrac : (T : ℝ) / (Nat.lcm (q : ℕ) (r : ℕ) : ℝ) ≤
        (D : ℕ) * (T : ℝ) / (((q : ℕ) : ℝ) * (r : ℕ)) := by
      rw [div_le_div_iff₀ hlpos (mul_pos hqpos hrpos)]
      calc
        _ = (Nat.gcd (q : ℕ) (r : ℕ) : ℝ) *
            ((T : ℝ) * (Nat.lcm (q : ℕ) (r : ℕ) : ℝ)) := by rw [← hmul]; ring
        _ ≤ (D : ℕ) * ((T : ℝ) * (Nat.lcm (q : ℕ) (r : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (Nat.cast_nonneg T) hlpos.le)
        _ = _ := by ring
    calc
      _ ≤ ((T / Nat.lcm (q : ℕ) (r : ℕ) + 1 : ℕ) : ℝ) := by
        exact_mod_cast jointDivisorCount_le_lcm P.left P.right T q r
      _ ≤ (T : ℝ) / (Nat.lcm (q : ℕ) (r : ℕ) : ℝ) + 1 := by
        push_cast
        exact add_le_add Nat.cast_div_le (le_refl (1 : ℝ))
      _ ≤ _ := add_le_add hfrac le_rfl
  · have hz : jointDivisorCount P.left P.right T q r = 0 := by
      rw [jointDivisorCount, not_nonempty_iff_eq_empty.mp h, card_empty]
    rw [hz, Nat.cast_zero]
    positivity

private theorem sum_inv_sq_le_two (R : ℕ+) :
    (∑ d ∈ Icc 1 (R : ℕ), 1 / (d : ℝ) ^ 2) ≤ 2 := by
  have hs : Icc 1 (R : ℕ) = insert 1 (Icc 2 (R : ℕ)) := by
    ext d
    simp only [mem_Icc, mem_insert]
    have := R.pos
    omega
  rw [hs, sum_insert (by simp : 1 ∉ Icc 2 (R : ℕ))]
  have h := RHTower.sum_inv_sq_tail_le (D := 1) (by omega) (R : ℕ)
  norm_num only [Nat.cast_one, one_pow, div_self (one_ne_zero : (1 : ℝ) ≠ 0)] at h ⊢
  linarith only [h]

private theorem abs_approx_le_divisor_count (n : ℕ+) (R : ℕ) :
    |approx R n| ≤ (((Icc 1 R).filter (fun d => d * d ∣ (n : ℕ))).card : ℝ) := by
  rw [approx, abs_mul, abs_liouville_eq_one, one_mul]
  calc
    _ ≤ ∑ d ∈ (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)), |(μ d : ℝ)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ (Icc 1 R).filter (fun d => d * d ∣ (n : ℕ)), (1 : ℝ) :=
      sum_le_sum fun d _ => abs_moebius_le_one d
    _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one]

/-- Multiplying the two local divisor counts and summing counts each joint incidence once. -/
theorem sum_square_divisor_counts_mul (F G : Row) (T R S M : ℕ) :
    (∑ t ∈ Icc 1 T,
      (((Icc 1 R).filter (fun d => d * d ∣ F.eval t)).card : ℝ) *
        (((Icc (S + 1) M).filter (fun e => e * e ∣ G.eval t)).card : ℝ)) =
      ∑ d ∈ Icc 1 R, ∑ e ∈ Icc (S + 1) M,
        (jointDivisorCount F G T (d * d) (e * e) : ℝ) := by
  have hpoint (t : ℕ) :
      (((Icc 1 R).filter (fun d => d * d ∣ F.eval t)).card : ℝ) *
          (((Icc (S + 1) M).filter (fun e => e * e ∣ G.eval t)).card : ℝ) =
        ∑ d ∈ Icc 1 R, ∑ e ∈ Icc (S + 1) M,
          if d * d ∣ F.eval t ∧ e * e ∣ G.eval t then (1 : ℝ) else 0 := by
    have hF : (((Icc 1 R).filter (fun d => d * d ∣ F.eval t)).card : ℝ) =
        ∑ d ∈ Icc 1 R, if d * d ∣ F.eval t then (1 : ℝ) else 0 := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
    have hG : (((Icc (S + 1) M).filter (fun e => e * e ∣ G.eval t)).card : ℝ) =
        ∑ e ∈ Icc (S + 1) M, if e * e ∣ G.eval t then (1 : ℝ) else 0 := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
    rw [hF, hG, sum_mul_sum]
    apply sum_congr rfl
    intro d _
    apply sum_congr rfl
    intro e _
    by_cases hd : d * d ∣ F.eval t <;> by_cases he : e * e ∣ G.eval t <;>
      simp only [hd, he, and_self, and_true, and_false, if_true, if_false,
        mul_zero, mul_one]
  simp_rw [hpoint]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [jointDivisorCount, ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]

private theorem sum_pair_inv_sq (R S M : ℕ) (A : ℝ) :
    (∑ d ∈ Icc 1 R, ∑ e ∈ Icc (S + 1) M,
      (A / ((d : ℝ) ^ 2 * (e : ℝ) ^ 2) + 1)) =
      A * ((∑ d ∈ Icc 1 R, 1 / (d : ℝ) ^ 2) *
        (∑ e ∈ Icc (S + 1) M, 1 / (e : ℝ) ^ 2)) +
          (R : ℝ) * ((Icc (S + 1) M).card : ℝ) := by
  calc
    _ = (∑ d ∈ Icc 1 R, ∑ e ∈ Icc (S + 1) M,
        A / ((d : ℝ) ^ 2 * (e : ℝ) ^ 2)) +
          ∑ _d ∈ Icc 1 R, ∑ _e ∈ Icc (S + 1) M, (1 : ℝ) := by
      simp only [sum_add_distrib]
    _ = _ := by
      congr 1
      · rw [sum_mul_sum, mul_sum]
        apply sum_congr rfl
        intro d _
        rw [mul_sum]
        apply sum_congr rfl
        intro e _
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      · simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel, mul_one]

/-- Retaining both divisor constraints replaces the truncation-size loss by the determinant. -/
theorem Frame.sum_weighted_error_le {D : ℕ+} (P : Frame D) (T : ℕ) (R S : ℕ+) :
    (∑ t ∈ Icc 1 T, |approx R (P.left.eval t)| *
      |(μ (P.right.eval t) : ℝ) - approx S (P.right.eval t)|) ≤
      (2 : ℝ) * (D : ℕ) * (T : ℝ) / (S : ℕ) +
        (R : ℕ) * (Nat.sqrt (P.right.eval T) : ℝ) := by
  have hpoint : ∀ t ∈ Icc 1 T,
      |approx R (P.left.eval t)| *
          |(μ (P.right.eval t) : ℝ) - approx S (P.right.eval t)| ≤
        (((Icc 1 (R : ℕ)).filter (fun d => d * d ∣ P.left.eval t)).card : ℝ) *
          (((Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).filter
            (fun e => e * e ∣ P.right.eval t)).card : ℝ) := by
    intro t ht
    have htpos : 0 < t := (mem_Icc.mp ht).1
    have hleft := abs_approx_le_divisor_count
      ⟨P.left.eval t, P.left.eval_pos ⟨t, htpos⟩⟩ (R : ℕ)
    have hright := abs_moebius_sub_approx_le
      ⟨P.right.eval t, P.right.eval_pos ⟨t, htpos⟩⟩ (S : ℕ)
    have hsub :
        (Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval t))).filter
            (fun e => e * e ∣ P.right.eval t) ⊆
          (Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).filter
            (fun e => e * e ∣ P.right.eval t) := by
      intro e he
      rcases mem_filter.mp he with ⟨hI, hdiv⟩
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hI).1,
        (mem_Icc.mp hI).2.trans
          (Nat.sqrt_le_sqrt (P.right.eval_mono (mem_Icc.mp ht).2))⟩, hdiv⟩
    have hcard :
        (((Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval t))).filter
            (fun e => e * e ∣ P.right.eval t)).card : ℝ) ≤
          (((Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).filter
            (fun e => e * e ∣ P.right.eval t)).card : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact mul_le_mul hleft (hright.trans hcard) (abs_nonneg _) (Nat.cast_nonneg _)
  have htailcard :
      ((Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).card : ℝ) ≤
        (Nat.sqrt (P.right.eval T) : ℝ) := by
    have h : (Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).card ≤
        Nat.sqrt (P.right.eval T) := by rw [Nat.card_Icc]; omega
    exact_mod_cast h
  have htailnn : 0 ≤ ∑ e ∈ Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T)),
      1 / (e : ℝ) ^ 2 := sum_nonneg fun _ _ => by positivity
  have hprod := mul_le_mul (sum_inv_sq_le_two R)
    (RHTower.sum_inv_sq_tail_le S.pos (Nat.sqrt (P.right.eval T))) htailnn
      (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ ∑ t ∈ Icc 1 T,
        (((Icc 1 (R : ℕ)).filter (fun d => d * d ∣ P.left.eval t)).card : ℝ) *
          (((Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).filter
            (fun e => e * e ∣ P.right.eval t)).card : ℝ) := sum_le_sum hpoint
    _ = ∑ d ∈ Icc 1 (R : ℕ), ∑ e ∈ Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T)),
        (jointDivisorCount P.left P.right T (d * d) (e * e) : ℝ) :=
      sum_square_divisor_counts_mul P.left P.right T R S (Nat.sqrt (P.right.eval T))
    _ ≤ ∑ d ∈ Icc 1 (R : ℕ), ∑ e ∈ Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T)),
        ((D : ℕ) * (T : ℝ) / ((d : ℝ) ^ 2 * (e : ℝ) ^ 2) + 1) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      have hdpos : 0 < d := (mem_Icc.mp hd).1
      have hepos : 0 < e := by have := (mem_Icc.mp he).1; omega
      have h := P.jointDivisorCount_le T ⟨d * d, Nat.mul_pos hdpos hdpos⟩
        ⟨e * e, Nat.mul_pos hepos hepos⟩
      change (jointDivisorCount P.left P.right T (d * d) (e * e) : ℝ) ≤
        (D : ℕ) * (T : ℝ) / (((d * d : ℕ) : ℝ) * ((e * e : ℕ) : ℝ)) + 1 at h
      simpa only [Nat.cast_mul, pow_two] using h
    _ = (D : ℕ) * (T : ℝ) *
        ((∑ d ∈ Icc 1 (R : ℕ), 1 / (d : ℝ) ^ 2) *
          (∑ e ∈ Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T)), 1 / (e : ℝ) ^ 2)) +
            (R : ℕ) * ((Icc ((S : ℕ) + 1) (Nat.sqrt (P.right.eval T))).card : ℝ) :=
      sum_pair_inv_sq R S (Nat.sqrt (P.right.eval T)) ((D : ℕ) * (T : ℝ))
    _ ≤ (D : ℕ) * (T : ℝ) * (2 * (1 / (S : ℕ))) +
        (R : ℕ) * (Nat.sqrt (P.right.eval T) : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hprod (by positivity))
        (mul_le_mul_of_nonneg_left htailcard (Nat.cast_nonneg _))
    _ = _ := by ring

private theorem abs_product_error_le_weighted (n m : ℕ+) (R S : ℕ) :
    |(μ n : ℝ) * (μ m : ℝ) - approx R n * approx S m| ≤
      |(μ n : ℝ) - approx R n| + |approx R n| * |(μ m : ℝ) - approx S m| := by
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
        |approx R n| * |(μ m : ℝ) - approx S m| :=
      add_le_add (mul_le_mul_of_nonneg_left (abs_moebius_le_one m) (abs_nonneg _)) le_rfl
    _ = _ := by rw [mul_one]

/-- Determinant-sensitive transfer keeps the joint square-divisor incidence in the product error. -/
theorem Frame.abs_correlation_sub_le {D : ℕ+} (P : Frame D) (T : ℕ) (R S : ℕ+) :
    |moebiusCorrelation P.left P.right T - liouvilleCorrelation P.left P.right T R S| ≤
      (T : ℝ) / (R : ℕ) + (Nat.sqrt (P.left.eval T) : ℝ) +
        ((2 : ℝ) * (D : ℕ) * (T : ℝ) / (S : ℕ) +
          (R : ℕ) * (Nat.sqrt (P.right.eval T) : ℝ)) := by
  rw [← sum_approx_mul_eq, moebiusCorrelation, ← sum_sub_distrib]
  calc
    _ ≤ ∑ t ∈ Icc 1 T,
        |(μ (P.left.eval t) : ℝ) * (μ (P.right.eval t) : ℝ) -
          approx R (P.left.eval t) * approx S (P.right.eval t)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Icc 1 T,
        (|(μ (P.left.eval t) : ℝ) - approx R (P.left.eval t)| +
          |approx R (P.left.eval t)| *
            |(μ (P.right.eval t) : ℝ) - approx S (P.right.eval t)|) := by
      apply sum_le_sum
      intro t ht
      have htpos : 0 < t := (mem_Icc.mp ht).1
      exact abs_product_error_le_weighted ⟨P.left.eval t, P.left.eval_pos ⟨t, htpos⟩⟩
        ⟨P.right.eval t, P.right.eval_pos ⟨t, htpos⟩⟩ R S
    _ = (∑ t ∈ Icc 1 T, |(μ (P.left.eval t) : ℝ) - approx R (P.left.eval t)|) +
        ∑ t ∈ Icc 1 T, |approx R (P.left.eval t)| *
          |(μ (P.right.eval t) : ℝ) - approx S (P.right.eval t)| := by rw [sum_add_distrib]
    _ ≤ _ := add_le_add (sum_abs_moebius_sub_approx_le P.left T R)
      (P.sum_weighted_error_le T R S)

/-- Equal square-divisor cutoffs suffice whenever the determinant is nonzero. -/
theorem Frame.abs_correlation_sub_same_cutoff_le {D : ℕ+} (P : Frame D) (T : ℕ) (R : ℕ+) :
    |moebiusCorrelation P.left P.right T - liouvilleCorrelation P.left P.right T R R| ≤
      (1 + (2 : ℝ) * (D : ℕ)) * (T : ℝ) / (R : ℕ) + (Nat.sqrt (P.left.eval T) : ℝ) +
        (R : ℕ) * (Nat.sqrt (P.right.eval T) : ℝ) := by
  calc
    _ ≤ (T : ℝ) / (R : ℕ) + (Nat.sqrt (P.left.eval T) : ℝ) +
        ((2 : ℝ) * (D : ℕ) * (T : ℝ) / (R : ℕ) +
          (R : ℕ) * (Nat.sqrt (P.right.eval T) : ℝ)) := P.abs_correlation_sub_le T R R
    _ = _ := by ring

/-- At determinant four, the equal-cutoff projection error has coefficient nine. -/
theorem abs_correlation_sub_same_cutoff_det_four_le (P : Frame 4) (T : ℕ) (R : ℕ+) :
    |moebiusCorrelation P.left P.right T - liouvilleCorrelation P.left P.right T R R| ≤
      9 * (T : ℝ) / (R : ℕ) + (Nat.sqrt (P.left.eval T) : ℝ) +
        (R : ℕ) * (Nat.sqrt (P.right.eval T) : ℝ) := by
  convert P.abs_correlation_sub_same_cutoff_le T R using 1
  norm_num

end

end TwinPrime.AffineSquarefree
