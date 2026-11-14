import GaloisForLFunctions.HTGeometry.Arithmetic.LogarithmicPrecision
import GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic.CongruentParameter
import Mathlib.Data.Nat.Choose.Basic

/-!
# Congruent-curve logarithmic truncations

The logarithmic terms are
`(-1)^j choose(2j,j) e^(2j) z^(4j+1)/(4j+1)`. At odd primes, every
nonempty truncation has the valuation of `z`. Terms above degree `K`
change its value only at precision `v_p(z)+K` when `p>K+1`.
At a pole of a point on `y²=x³-e²x`, the truncation therefore has
valuation exactly `-v_p(x)/2`.
-/

namespace GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic

open HTGeometry.Arithmetic

/-- One logarithmic term, with its integral binomial numerator explicit. -/
def congruentLogTerm (e z : ℚ) (j : ℕ) : ℚ :=
  (((-1 : ℤ) ^ j * (Nat.choose (2 * j) j : ℤ) : ℤ) : ℚ) *
    e ^ (2 * j) / ((4 * j + 1 : ℕ) : ℚ) * z ^ (4 * j + 1)

@[simp] theorem congruentLogTerm_zero (e z : ℚ) : congruentLogTerm e z 0 = z := by
  simp [congruentLogTerm]

/-- The first `N` nonzero-degree positions of the logarithmic series. -/
def congruentLogTruncation (e z : ℚ) (N : ℕ) : ℚ :=
  ∑ j ∈ Finset.range N, congruentLogTerm e z j

variable {p : ℕ} [Fact p.Prime]

theorem congruentLog_tail_precision (e z : ℚ) (s : Finset ℕ) (K : ℕ)
    (he : 0 ≤ padicValRat p e) (hz : 1 ≤ padicValRat p z)
    (hp : K + 1 < p) (hs : ∀ j ∈ s, K < 4 * j + 1) :
    (∑ j ∈ s, congruentLogTerm e z j) = 0 ∨
      padicValRat p z + (K : ℤ) ≤ padicValRat p (∑ j ∈ s, congruentLogTerm e z j) :=
  logarithmic_tail_precision s (fun j => (-1 : ℤ) ^ j * (Nat.choose (2 * j) j : ℤ))
    (fun j => 2 * j) (fun j => 4 * j + 1) e z K he hz hp hs

/-- Enlarging a truncation changes it only beyond the precision secured
by its first omitted degree. -/
theorem congruentLogTruncation_difference_precision (e z : ℚ) (M N K : ℕ)
    (he : 0 ≤ padicValRat p e) (hz : 1 ≤ padicValRat p z)
    (hp : K + 1 < p) (hMN : M ≤ N) (hK : K < 4 * M + 1) :
    congruentLogTruncation e z N - congruentLogTruncation e z M = 0 ∨
      padicValRat p z + (K : ℤ) ≤
        padicValRat p (congruentLogTruncation e z N - congruentLogTruncation e z M) := by
  have htail := congruentLog_tail_precision e z (Finset.Ico M N) K he hz hp (by
    intro j hj
    have hMj := (Finset.mem_Ico.mp hj).1
    omega)
  rwa [Finset.sum_Ico_eq_sub _ hMN] at htail

/-- At an odd prime, the linear term strictly dominates every higher
term of every nonempty truncation. -/
theorem congruentLogTruncation_val (e z : ℚ) (N : ℕ)
    (he : 0 ≤ padicValRat p e) (hz : 1 ≤ padicValRat p z)
    (hp : 2 < p) (hN : 0 < N) :
    congruentLogTruncation e z N ≠ 0 ∧
      padicValRat p (congruentLogTruncation e z N) = padicValRat p z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let tail := ∑ j ∈ Finset.Ico 1 N, congruentLogTerm e z j
  have heq : congruentLogTruncation e z N = z + tail := by
    have h := Finset.sum_range_add_sum_Ico (congruentLogTerm e z) (by omega : 1 ≤ N)
    simpa only [congruentLogTruncation, Finset.sum_range_one, congruentLogTerm_zero] using h.symm
  rcases congruentLog_tail_precision e z (Finset.Ico 1 N) 1 he hz hp (by
      intro j hj
      have hjpos := (Finset.mem_Ico.mp hj).1
      omega) with htzero | htval
  · change tail = 0 at htzero
    rw [heq, htzero, add_zero]
    exact ⟨hz0, rfl⟩
  · change padicValRat p z + (1 : ℕ) ≤ padicValRat p tail at htval
    have ht0 : tail ≠ 0 := by intro h; simp only [h, padicValRat.zero] at htval; omega
    have hne : padicValRat p z ≠ padicValRat p tail := by omega
    have hsum := add_ne_zero_of_val_ne hne
    rw [heq]
    refine ⟨hsum, ?_⟩
    rw [padicValRat.add_eq_min hsum hz0 ht0 hne, min_eq_left (by omega)]

/-- The truncation through degree `K` retains `K` additional digits in
comparison with every longer truncation. -/
theorem congruentLog_degree_precision (e z : ℚ) (K N : ℕ)
    (he : 0 ≤ padicValRat p e) (hz : 1 ≤ padicValRat p z)
    (hp : K + 1 < p) (hK : 1 ≤ K) (hN : (K - 1) / 4 + 1 ≤ N) :
    congruentLogTruncation e z N - congruentLogTruncation e z ((K - 1) / 4 + 1) = 0 ∨
      padicValRat p z + (K : ℤ) ≤ padicValRat p
        (congruentLogTruncation e z N - congruentLogTruncation e z ((K - 1) / 4 + 1)) :=
  congruentLogTruncation_difference_precision e z _ N K he hz hp hN (by omega)

/-- On the congruent curve, logarithmic truncations recover the exact
half-pole order of the x-coordinate at every odd prime. -/
theorem congruentLogTruncation_curve_pole {e x y : ℚ} (N : ℕ)
    (he : 0 ≤ padicValRat p e) (hx : padicValRat p x < 0)
    (hcurve : y ^ 2 = x ^ 3 - e ^ 2 * x) (hp : 2 < p) (hN : 0 < N) :
    congruentLogTruncation e (congruentParameter x y) N ≠ 0 ∧
      2 * padicValRat p (congruentLogTruncation e (congruentParameter x y) N) =
        -padicValRat p x := by
  obtain ⟨_, hval, hz⟩ := congruentParameter_val_of_neg he hx hcurve
  obtain ⟨hne, hlog⟩ := congruentLogTruncation_val e (congruentParameter x y) N he
    (by omega) hp hN
  exact ⟨hne, by rw [hlog]; exact hval⟩

#print axioms congruentLog_degree_precision
#print axioms congruentLogTruncation_curve_pole

end GaloisForLFunctions.KodairaParshinAbc.LocalArithmetic
