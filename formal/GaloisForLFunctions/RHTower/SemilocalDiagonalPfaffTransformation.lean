import GaloisForLFunctions.RHTower.ScaledTerminatingHypergeometricLimit
import GaloisForLFunctions.RHTower.SemilocalBoostDiagonalClosedForm

/-!
# The Pfaff transformation of the diagonal cosine moments

The Lean closed form of the diagonal boost element is the `τ`-form
`S_n(τ) = Σ_{l ≤ n} C(n,l) ((−(n+½)) choose l) τ^{2l}`, in which the terms are huge and cancel.  The
Pfaff transformation `₂F₁(−n, b; c; x) = ((c−b)_n/(c)_n) ₂F₁(−n, b; b−c−n+1; 1−x)` converts it to the
`σ`-form

`S_n(τ) = (−1)^n C_n · ₂F₁(−n, n+½; ½; 1 − τ²)`,   `C_n = binom(2n,n)/4^n`,

whose terms are bounded when `n σ` is bounded (`σ² = 1 − τ²`).  This is what the Mehler–Heine
mechanism needs.  The proof expands `x^l` in powers of `1 − x`, swaps the double sum, and applies the
Chu–Vandermonde identity (`Ring.add_choose_eq`).
-/

open Finset
open scoped BigOperators

namespace RHTower

namespace ScaledHypergeometric

/-- `x^l` expanded in powers of `1 − x`. -/
theorem pow_eq_sum_one_sub (x : ℝ) (l : ℕ) :
    x ^ l = ∑ m ∈ range (l + 1), (-1) ^ m * (l.choose m : ℝ) * (1 - x) ^ m := by
  have h := add_pow (-(1 - x)) 1 l
  rw [show -(1 - x) + 1 = x by ring] at h
  rw [h]
  apply sum_congr rfl
  intro m _
  rw [neg_pow]
  ring

/-- Chu–Vandermonde: `Σ_{i ≤ N} C(N,i) ((−b) choose (m+i)) = ((N − b) choose (N + m))`. -/
theorem sum_choose_mul_ringChoose (N m : ℕ) (b : ℝ) :
    ∑ i ∈ range (N + 1), (N.choose i : ℝ) * Ring.choose (-b) (m + i) =
      Ring.choose ((N : ℝ) - b) (N + m) := by
  have h := Ring.add_choose_eq (R := ℝ) (r := (N : ℝ)) (s := -b) (N + m) (Commute.all _ _)
  rw [show (N : ℝ) + -b = (N : ℝ) - b by ring] at h
  rw [h, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Ring.choose_natCast]
  symm
  rw [Nat.succ_eq_add_one, show N + m + 1 = (N + 1) + m by ring, sum_range_add]
  have hz : ∑ k ∈ range m, ((N.choose (N + 1 + k) : ℕ) : ℝ) *
      Ring.choose (-b) (N + m - (N + 1 + k)) = 0 := by
    apply sum_eq_zero
    intro k _
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hz, add_zero]
  conv_lhs => rw [← sum_range_reflect]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [show N + 1 - 1 - i = N - i by omega, Nat.choose_symm (by omega : i ≤ N),
    show N + m - (N - i) = m + i by omega]

/-- **The Pfaff transformation for terminating sums with a natural first parameter.** -/
theorem pfaff_transform (n : ℕ) (b x : ℝ) :
    ∑ l ∈ range (n + 1), (n.choose l : ℝ) * Ring.choose (-b) l * x ^ l =
      ∑ m ∈ range (n + 1), (-1) ^ m * (n.choose m : ℝ) *
        Ring.choose ((n : ℝ) - m - b) n * (1 - x) ^ m := by
  simp_rw [pow_eq_sum_one_sub x, mul_sum]
  rw [sum_comm' (t' := range (n + 1)) (s' := fun m => Ico m (n + 1)) (by
    intro l m
    simp only [mem_range, mem_Ico]
    omega)]
  apply sum_congr rfl
  intro m hm
  rw [mem_range] at hm
  rw [sum_Ico_eq_sum_range, show n + 1 - m = n - m + 1 by omega]
  have hfac : ∀ i ∈ range (n - m + 1),
      (n.choose (m + i) : ℝ) * ((m + i).choose m : ℝ) =
        (n.choose m : ℝ) * ((n - m).choose i : ℝ) := by
    intro i hi
    rw [mem_range] at hi
    have := Nat.choose_mul (n := n) (k := m + i) (s := m) (by omega)
    rw [show m + i - m = i by omega] at this
    exact_mod_cast this
  have hrw : (∑ i ∈ range (n - m + 1), (n.choose (m + i) : ℝ) * Ring.choose (-b) (m + i) *
      ((-1) ^ m * ((m + i).choose m : ℝ) * (1 - x) ^ m)) =
      (-1) ^ m * (n.choose m : ℝ) * (1 - x) ^ m *
        ∑ i ∈ range (n - m + 1), ((n - m).choose i : ℝ) * Ring.choose (-b) (m + i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have := hfac i hi
    linear_combination (Ring.choose (-b) (m + i) * (-1) ^ m * (1 - x) ^ m) * this
  rw [hrw, sum_choose_mul_ringChoose, show n - m + m = n by omega,
    Nat.cast_sub (by omega : m ≤ n)]
  ring

/-- The `σ`-form coefficient identity `((−(m+½)) choose n) = (−1)^n C_n (n+½)_m / (½)_m`. -/
theorem ringChoose_neg_add_half (n m : ℕ) :
    Ring.choose (-((m : ℝ) + 1 / 2)) n =
      (-1) ^ n * (Nat.centralBinom n / 4 ^ n : ℝ) * rising ((n : ℝ) + 1 / 2) m / rising (1 / 2) m := by
  rw [ringChoose_neg_eq_rising, normalizedCentralBinom_eq_rising_half_div]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hr : rising (1 / 2) m ≠ 0 := (rising_pos (by norm_num) m).ne'
  have key : rising ((m : ℝ) + 1 / 2) n * rising (1 / 2) m =
      rising (1 / 2) n * rising ((n : ℝ) + 1 / 2) m := by
    have h1 := rising_add (1 / 2) m n
    have h2 := rising_add (1 / 2) n m
    rw [add_comm m n] at h1
    rw [show (1 / 2 : ℝ) + m = (m : ℝ) + 1 / 2 by ring] at h1
    rw [show (1 / 2 : ℝ) + n = (n : ℝ) + 1 / 2 by ring] at h2
    linear_combination h2 - h1
  set A := rising ((m : ℝ) + 1 / 2) n with hA
  set B := rising ((n : ℝ) + 1 / 2) m with hB
  set R := rising (1 / 2) m with hR
  set Q := rising (1 / 2) n with hQ
  field_simp
  linear_combination key

/-- **The diagonal sum in `σ`-form:**
`Σ_{l ≤ n} C(n,l) ((−(n+½)) choose l) x^l = (−1)^n C_n · ₂F₁(−n, n+½; ½; 1 − x)`. -/
theorem semilocalDiagonalSum_eq_hypSumSq (n : ℕ) (x : ℝ) :
    ∑ l ∈ range (n + 1), (n.choose l : ℝ) * Ring.choose (-((n : ℝ) + 1 / 2)) l * x ^ l =
      (-1) ^ n * (Nat.centralBinom n / 4 ^ n : ℝ) * hypSumSq n (1 / 2) (1 / 2) (1 - x) := by
  rw [pfaff_transform n ((n : ℝ) + 1 / 2) x]
  unfold hypSumSq
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rw [show (n : ℝ) - m - ((n : ℝ) + 1 / 2) = -((m : ℝ) + 1 / 2) by ring, ringChoose_neg_add_half,
    fallingNat_eq_factorial_mul_choose]
  have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hr : rising (1 / 2) m ≠ 0 := (rising_pos (by norm_num) m).ne'
  field_simp
  try ring

/-- **The diagonal cosine moments in `σ`-form:**
`∫ p_n² cos(δ s) dμ = (cosh δ)^{-1/2} (−1)^n C_n · ₂F₁(−n, n+½; ½; sech² δ)`. -/
theorem cosineDiagonalMoment_eq_hypSum (δ : ℝ) (n : ℕ) :
    CosineModeResponse.cosineDiagonalMoment δ n =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) * ((-1) ^ n * (Nat.centralBinom n / 4 ^ n : ℝ) *
        hypSum n (1 / 2) (1 / 2) (1 / Real.cosh δ)) := by
  rw [MeixnerPollaczek.cosineDiagonalMoment_eq]
  have h := semilocalDiagonalSum_eq_hypSumSq n (Real.tanh δ ^ 2)
  rw [h, hypSum_eq_hypSumSq]
  congr 3
  have hc : Real.cosh δ ≠ 0 := (Real.cosh_pos δ).ne'
  rw [Real.tanh_eq_sinh_div_cosh, div_pow, one_div, inv_pow]
  field_simp
  linear_combination Real.cosh_sq δ

end ScaledHypergeometric

end RHTower
