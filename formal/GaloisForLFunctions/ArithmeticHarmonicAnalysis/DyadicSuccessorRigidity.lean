import GaloisForLFunctions.ArithmeticCorrelationGeometry.MultiplicativeObservationIsGaugeInvariant

/-!
# Logarithmic reconstruction from finite successor defects

The largest successor defect through cutoff `N` controls every observed
gauge value at binary depth `k` with loss `2k`. Multiplicativity halves
the integer argument at each step. The zero-defect fibre is exactly the
set of twists trivial at primes through `N`; larger primes stay free.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open ArithmeticCorrelationGeometry

/-- The additive defect of the multiplicative gauge twist at one successor step. -/
def successorDefect (x : GaugeTorus) (n : ℕ) : ℂ := twist x (n + 1) - twist x n

/-- The largest observed successor defect, with empty maximum zero. -/
def successorRadius (x : GaugeTorus) (N : ℕ) : ℝ :=
  ((Ico 1 N).sup fun n => ‖successorDefect x n‖₊ : NNReal)

theorem successorRadius_nonneg (x : GaugeTorus) (N : ℕ) : 0 ≤ successorRadius x N :=
  NNReal.coe_nonneg _

theorem norm_successorDefect_le_radius (x : GaugeTorus) {n N : ℕ}
    (hn : n ∈ Ico 1 N) : ‖successorDefect x n‖ ≤ successorRadius x N := by
  unfold successorRadius
  exact_mod_cast (Finset.le_sup (f := fun m => ‖successorDefect x m‖₊) hn)

private theorem norm_twist_two_sub_one_le_radius (x : GaugeTorus) {N : ℕ} (hN : 2 ≤ N) :
    ‖twist x 2 - 1‖ ≤ successorRadius x N := by
  have h := norm_successorDefect_le_radius x (n := 1) (N := N)
    (mem_Ico.mpr ⟨le_rfl, by omega⟩)
  simpa only [successorDefect, twist_one] using h

private theorem norm_twist_double_sub_one_le (x : GaugeTorus) {m : ℕ} (hm : 0 < m) :
    ‖twist x (2 * m) - 1‖ ≤ ‖twist x m - 1‖ + ‖twist x 2 - 1‖ := by
  rw [twist_mul x (by omega : (2 : ℕ) ≠ 0) hm.ne']
  calc
    _ = ‖twist x 2 * (twist x m - 1) + (twist x 2 - 1)‖ := by congr 1; ring
    _ ≤ ‖twist x 2 * (twist x m - 1)‖ + ‖twist x 2 - 1‖ := norm_add_le _ _
    _ = _ := by rw [norm_mul, norm_twist, one_mul]

/-- Multiplicative dilation reduces successor reconstruction loss to binary depth. -/
theorem norm_twist_sub_one_le_dyadic_radius (x : GaugeTorus) (N k : ℕ)
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) (hnk : n ≤ 2 ^ k) :
    ‖twist x n - 1‖ ≤ 2 * (k : ℝ) * successorRadius x N := by
  induction k generalizing n with
  | zero =>
    have hnk' : n ≤ 1 := by simpa only [pow_zero] using hnk
    have h1 : n = 1 := by omega
    rw [h1, twist_one, sub_self, norm_zero, Nat.cast_zero, mul_zero, zero_mul]
  | succ k ih =>
    by_cases h1 : n = 1
    · rw [h1, twist_one, sub_self, norm_zero]
      exact mul_nonneg (by positivity) (successorRadius_nonneg x N)
    have hn2 : 2 ≤ n := by omega
    have hmpos : 0 < n / 2 := by omega
    have hmN : n / 2 ≤ N := (Nat.div_le_self n 2).trans hnN
    have hmk : n / 2 ≤ 2 ^ k := by rw [pow_succ] at hnk; omega
    have hhalf := ih hmpos hmN hmk
    have htwo := norm_twist_two_sub_one_le_radius x (hn2.trans hnN)
    have hdouble := norm_twist_double_sub_one_le x hmpos
    have hstep : ‖twist x n - twist x (2 * (n / 2))‖ ≤ successorRadius x N := by
      have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hmod with heven | hodd
      · have he : n = 2 * (n / 2) := by omega
        rw [← he, sub_self, norm_zero]
        exact successorRadius_nonneg x N
      · have he : n = 2 * (n / 2) + 1 := by omega
        have hmem : 2 * (n / 2) ∈ Ico 1 N := mem_Ico.mpr ⟨by omega, by omega⟩
        have h := norm_successorDefect_le_radius x hmem
        simpa only [successorDefect, ← he] using h
    have htriangle := norm_add_le (twist x n - twist x (2 * (n / 2)))
      (twist x (2 * (n / 2)) - 1)
    rw [sub_add_sub_cancel] at htriangle
    push_cast
    linarith only [htriangle, hstep, hdouble, hhalf, htwo]

/-- Zero observed successor defect means every observed arithmetic value is one. -/
theorem successorRadius_eq_zero_iff (x : GaugeTorus) (N : ℕ) :
    successorRadius x N = 0 ↔ ∀ n, 0 < n → n ≤ N → twist x n = 1 := by
  constructor
  · intro h n hn hnN
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn0 : n = 0
      · subst n; exact twist_one x
      have hnpos : 0 < n := by omega
      have hprev := ih hnpos (by omega)
      have hd := norm_successorDefect_le_radius x (n := n) (N := N)
        (mem_Ico.mpr ⟨hnpos, by omega⟩)
      rw [h] at hd
      have hz := norm_eq_zero.mp (le_antisymm hd (norm_nonneg _))
      exact (sub_eq_zero.mp hz).trans hprev
  · intro h
    apply le_antisymm _ (successorRadius_nonneg x N)
    change (((Ico 1 N).sup fun n => ‖successorDefect x n‖₊ : NNReal) : ℝ) ≤ 0
    suffices (Ico 1 N).sup (fun n => ‖successorDefect x n‖₊) ≤ 0 by exact_mod_cast this
    apply Finset.sup_le
    intro n hn
    obtain ⟨hn1, hnN⟩ := mem_Ico.mp hn
    simp only [successorDefect, h (n + 1) (by omega) (by omega), h n hn1 hnN.le,
      sub_self, nnnorm_zero, le_refl]

/-- The zero-defect fibre fixes precisely the prime values visible below the cutoff. -/
theorem successorRadius_eq_zero_iff_prime (x : GaugeTorus) (N : ℕ) :
    successorRadius x N = 0 ↔ ∀ p, p.Prime → p ≤ N → twist x p = 1 := by
  rw [successorRadius_eq_zero_iff]
  constructor
  · exact fun h p hp hpN => h p hp.pos hpN
  · intro h n hn hnN
    induction n using induction_on_primes with
    | zero => omega
    | one => exact twist_one x
    | prime_mul p a hp ih =>
      have ha : 0 < a := Nat.pos_of_mul_pos_left hn
      have hpN : p ≤ N := (Nat.le_mul_of_pos_right p ha).trans hnN
      have haN : a ≤ N := (Nat.le_mul_of_pos_left a hp.pos).trans hnN
      rw [twist_mul x hp.ne_zero ha.ne', h p hp hpN, ih ha haN, one_mul]

/-- Dividing by the unit value at the second gauge point preserves the observation distance. -/
theorem norm_twist_sub_twist_eq (x y : GaugeTorus) (n : ℕ) :
    ‖twist x n - twist y n‖ = ‖twist (x - y) n - 1‖ := by
  have h := twist_add (x - y) y n
  rw [sub_add_cancel] at h
  calc
    _ = ‖(twist (x - y) n - 1) * twist y n‖ := by rw [h]; congr 1; ring
    _ = _ := by rw [norm_mul, norm_twist, mul_one]

/-- Finite successor observations control the distance between any two gauge twists. -/
theorem norm_twist_sub_twist_le_dyadic_radius (x y : GaugeTorus) (N k : ℕ)
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) (hnk : n ≤ 2 ^ k) :
    ‖twist x n - twist y n‖ ≤ 2 * (k : ℝ) * successorRadius (x - y) N := by
  rw [norm_twist_sub_twist_eq]
  exact norm_twist_sub_one_le_dyadic_radius (x - y) N k hn hnN hnk

/-- Two gauges have zero finite successor distance exactly when their observed prime values agree. -/
theorem successorRadius_sub_eq_zero_iff_prime (x y : GaugeTorus) (N : ℕ) :
    successorRadius (x - y) N = 0 ↔
      ∀ p, p.Prime → p ≤ N → twist x p = twist y p := by
  rw [successorRadius_eq_zero_iff_prime]
  constructor
  · intro h p hp hpN
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [norm_twist_sub_twist_eq, h p hp hpN, sub_self, norm_zero]
  · intro h p hp hpN
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← norm_twist_sub_twist_eq, h p hp hpN, sub_self, norm_zero]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
