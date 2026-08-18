import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# Support of the diagonalised Möbius sums

The inner sums of the Selberg diagonalisation vanish outside a finite squarefree range: they carry
the factor `μ(e)`, so they die when `e` is not squarefree, and their index set is empty when `e`
exceeds the window.  Hence the totient-weighted diagonal is a finite sum over squarefree `e ≤ N`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- Beyond the window there are no multiples to sum. -/
theorem filter_dvd_eq_empty_of_lt {e N : ℕ} (h : N < e) :
    (Finset.Icc 1 N).filter (fun m => e ∣ m) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
  obtain ⟨hmem, hdvd⟩ := Finset.mem_filter.mp hm
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hmem
  have hle : e ≤ m := Nat.le_of_dvd (by omega) hdvd
  omega

theorem sum_filter_dvd_eq_zero_of_lt {e N : ℕ} (h : N < e) (f : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), f m = 0 := by
  rw [filter_dvd_eq_empty_of_lt h, Finset.sum_empty]

/-- A non-squarefree modulus kills the whole inner Möbius sum. -/
theorem sum_filter_dvd_moebius_eq_zero_of_not_squarefree {e N : ℕ} (he : 0 < e)
    (h : ¬ Squarefree e) (g : ℕ → ℝ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), (μ m : ℝ) * g m = 0 := by
  classical
  rw [sum_filter_dvd_moebius_scaled he g]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : (μ e : ℤ) = 0 := moebius_eq_zero_of_not_squarefree h
  have h0R : ((μ e : ℤ) : ℝ) = 0 := by exact_mod_cast h0
  rw [h0R, zero_mul, zero_mul]

/-- **The diagonal is supported on squarefree moduli inside the window.** -/
theorem sum_filter_dvd_moebius_eq_zero {e N : ℕ} (he : 0 < e) (g : ℕ → ℝ)
    (h : ¬ Squarefree e ∨ N < e) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => e ∣ m), (μ m : ℝ) * g m = 0 := by
  rcases h with h | h
  · exact sum_filter_dvd_moebius_eq_zero_of_not_squarefree he h g
  · exact sum_filter_dvd_eq_zero_of_lt h _

end RHTower.Sieve
