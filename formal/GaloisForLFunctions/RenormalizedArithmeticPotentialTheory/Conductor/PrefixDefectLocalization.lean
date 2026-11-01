import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArithmeticTailPaysForItsLogarithmicMass

/-!
# Tail mass uses only the added prime edges

Keeping the upper-endpoint cutoff in Young's inequality pays the tail from
`D_N-D_M`. The full defect below the cutoff remains available.
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped Chebyshev
namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The logarithmic tail spends only prime-edge energy added above the cutoff. -/
theorem logarithmicTailMass_le_poleDefect_increment {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    logarithmicTailMass M N x ≤ (1 + 1 / u) * (poleDefect N x - poleDefect M x) +
      (1 + u) * cutoffPrimeCost M N * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hpoint : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      (if M < m * t then Λ t * x (m * t) ^ 2 else 0) ≤
        (1 + 1 / u) * (if M < m * t then
          Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0) +
        (1 + u) * (if M < m * t then Λ t * (x m / Real.sqrt t) ^ 2 else 0) := by
    intro m _ t _
    by_cases h : M < m * t
    · simp only [if_pos h]
      have hy : x (m * t) ^ 2 ≤
          (1 + 1 / u) * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          (1 + u) * (x m / Real.sqrt t) ^ 2 := by
        calc
          _ ≤ x (m * t) ^ 2 +
              ((x (m * t) - x m / Real.sqrt t) - u * (x m / Real.sqrt t)) ^ 2 / u :=
            le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hu.le)
          _ = _ := by field_simp [hu.ne']; ring
      have hh := mul_le_mul_of_nonneg_left hy (vonMangoldt_nonneg (n := t))
      calc
        _ ≤ Λ t * ((1 + 1 / u) * (x (m * t) - x m / Real.sqrt t) ^ 2 +
          (1 + u) * (x m / Real.sqrt t) ^ 2) := hh
        _ = _ := by ring
    · simp only [if_neg h, mul_zero, add_zero, le_refl]
  have hsum := sum_le_sum fun m hm => sum_le_sum fun t ht => hpoint m hm t ht
  simp only [sum_add_distrib, ← mul_sum] at hsum
  rw [← logarithmicTailMass_eq_edges] at hsum
  have hsplit := poleDefect_eq_cutoff_add_tail hMN x
  have hedge : (∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), if M < m * t then
      Λ t * (x (m * t) - x m / Real.sqrt t) ^ 2 else 0) = poleDefect N x - poleDefect M x := by
    linarith only [hsplit]
  rw [hedge] at hsum
  have hout := mul_le_mul_of_nonneg_left (outgoing_cutoff_edges_le hM hMN x)
    (show 0 ≤ 1 + u by positivity)
  linarith only [hsum, hout]

/-- The horizon logarithm on the tail preserves the whole prefix defect. -/
theorem log_mul_tail_mass_le_defect_increment {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (x : ℕ → ℝ) {u : ℝ} (hu : 0 < u) :
    Real.log N * (∑ n ∈ Icc 1 N, atomicTailCoefficients M x n ^ 2) ≤
      (1 + 1 / u) * (poleDefect N x - poleDefect M x) +
        ((1 + u) * cutoffPrimeCost M N + Real.log N - Real.log M) *
          (∑ n ∈ Icc 1 N, x n ^ 2) := by
  have hMNlog : Real.log M ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hMN)
  have hpoint : ∀ n ∈ Icc 1 N,
      Real.log N * atomicTailCoefficients M x n ^ 2 ≤
        (if M < n then Real.log n * x n ^ 2 else 0) +
          (Real.log N - Real.log M) * x n ^ 2 := by
    intro n _
    rw [atomicTailCoefficients_sq]
    by_cases hn : M < n
    · simp only [if_pos hn]
      have hl : Real.log M ≤ Real.log n :=
        Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast hn.le)
      nlinarith only [mul_nonneg (sub_nonneg.mpr hl) (sq_nonneg (x n))]
    · simp only [if_neg hn, mul_zero, zero_add]
      exact mul_nonneg (sub_nonneg.mpr hMNlog) (sq_nonneg _)
  have hsum := sum_le_sum hpoint
  simp only [sum_add_distrib, ← mul_sum] at hsum
  change Real.log N * _ ≤ logarithmicTailMass M N x + _ at hsum
  have htail := logarithmicTailMass_le_poleDefect_increment hM hMN x hu
  linarith only [hsum, htail]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.logarithmicTailMass_le_poleDefect_increment
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.log_mul_tail_mass_le_defect_increment
