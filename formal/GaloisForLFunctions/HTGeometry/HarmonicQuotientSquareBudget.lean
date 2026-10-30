import GaloisForLFunctions.HTGeometry.HarmonicQuotientTailBound
import GaloisForLFunctions.PNTPlus.Wiener

/-!
# Uniform square budgets for logarithmic quotient envelopes

An inverse logarithm at the complementary quotient has a summable square
under harmonic measure. Combining this with a moving quotient tail avoids
paying the full harmonic mass for a decaying row error.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HTGeometry

/-- The squared logarithmic envelope has uniformly bounded harmonic mass. -/
theorem harmonic_log_kernel_sum_le (S : Finset ℕ) {X : ℝ} (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ X) :
    (∑ n ∈ S, (1 / (n : ℝ)) / (1 + Real.log (X / n)) ^ 2) ≤
      1 + 2 * Real.pi ^ 2 := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hcheby : chebyWith 1 (fun _ : ℕ => (1 : ℂ)) := by
    intro n
    simp [cumsum]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / X)) ^ 2)⁻¹) := by
    simpa only [norm_one, one_div] using
      limiting_fourier_lim1_aux ⟨1, hcheby⟩ hX0 1 zero_le_one
  have hfull : (∑' n : ℕ, 1 / (n : ℝ) *
      (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / X)) ^ 2)⁻¹) ≤
      1 + 2 * Real.pi ^ 2 := by
    simpa only [norm_one, one_mul] using bound_sum_log' hcheby hX
  have hpoint (n : ℕ) (hn : n ∈ S) :
      (1 / (n : ℝ)) / (1 + Real.log (X / n)) ^ 2 ≤
        1 / (n : ℝ) *
          (1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / X)) ^ 2)⁻¹ := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hS n hn).1
    have ht : 0 ≤ Real.log (X / n) :=
      Real.log_nonneg ((one_le_div hn0).mpr (hS n hn).2)
    have hid : Real.log ((n : ℝ) / X) = -Real.log (X / n) := by
      rw [Real.log_div hn0.ne' hX0.ne', Real.log_div hX0.ne' hn0.ne']
      ring
    have hα0 : 0 ≤ 1 / (2 * Real.pi) := by positivity
    have hα1 : 1 / (2 * Real.pi) ≤ 1 := one_div_two_pi_mem_Ioo.2.le
    have hα : |1 / (2 * Real.pi) * Real.log ((n : ℝ) / X)| ≤ Real.log (X / n) := by
      rw [hid, abs_mul, abs_of_nonneg hα0, abs_neg, abs_of_nonneg ht]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hα1 ht
    have hsq := mul_self_le_mul_self (abs_nonneg _) hα
    simp only [← sq, sq_abs] at hsq
    have hden : 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / X)) ^ 2 ≤
        (1 + Real.log (X / n)) ^ 2 := by
      nlinarith only [hsq, ht]
    have hi := one_div_le_one_div_of_le
      (show 0 < 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / X)) ^ 2 by positivity) hden
    have hm := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1 / (n : ℝ) by positivity)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hm
  exact (sum_le_sum hpoint).trans
    ((Summable.sum_le_tsum S (fun n _ => by positivity) hsum).trans hfull)

/-- A logarithmic envelope above a quotient cutoff and a global bound give a
horizon-independent square budget apart from the logarithmic cutoff cost. -/
theorem sum_sq_le_harmonic_log_envelope {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T)
    {A B : ℝ} (R : ℕ → ℝ)
    (hglobal : ∀ n ∈ Icc 1 N, |R n| ≤ B / Real.sqrt n)
    (hgood : ∀ n ∈ Icc 1 N, T ≤ (N : ℝ) / n →
      |R n| ≤ (A / (1 + Real.log (((N : ℝ) / T) / n))) / Real.sqrt n) :
    (∑ n ∈ Icc 1 N, R n ^ 2) ≤
      A ^ 2 * (1 + 2 * Real.pi ^ 2) + B ^ 2 * (1 + Real.log (2 * T)) := by
  let S := (Icc 1 N).filter fun n : ℕ => T ≤ (N : ℝ) / n
  let U := (Icc 1 N).filter fun n : ℕ => (N : ℝ) / n < T
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hS (n : ℕ) (hn : n ∈ S) : 0 < n ∧ (n : ℝ) ≤ (N : ℝ) / T := by
    obtain ⟨hn, ht⟩ := mem_filter.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    refine ⟨(mem_Icc.mp hn).1, (le_div_iff₀ hT0).mpr ?_⟩
    have h := (le_div_iff₀ hn0).mp ht
    simpa only [mul_comm] using h
  have hkernel : (∑ n ∈ S, (1 / (n : ℝ)) /
      (1 + Real.log (((N : ℝ) / T) / n)) ^ 2) ≤ 1 + 2 * Real.pi ^ 2 := by
    by_cases hx : 1 ≤ (N : ℝ) / T
    · exact harmonic_log_kernel_sum_le S hx hS
    · have hempty : S = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (hS n hn).1
        exact hx (hn1.trans (hS n hn).2)
      rw [hempty, sum_empty]
      positivity
  have hsquare (n : ℕ) (C : ℝ) (hc : |R n| ≤ C / Real.sqrt n) :
      R n ^ 2 ≤ C ^ 2 / n := by
    have h := mul_self_le_mul_self (abs_nonneg _) hc
    simpa only [← sq, sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)] using h
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      R n ^ 2 ≤
        (if T ≤ (N : ℝ) / n then
          A ^ 2 * ((1 / (n : ℝ)) / (1 + Real.log (((N : ℝ) / T) / n)) ^ 2) else 0) +
        (if (N : ℝ) / n < T then B ^ 2 * (1 / (n : ℝ)) else 0) := by
    by_cases ht : T ≤ (N : ℝ) / n
    · rw [if_pos ht, if_neg (not_lt.mpr ht), add_zero]
      have h := hsquare n (A / (1 + Real.log (((N : ℝ) / T) / n))) (hgood n hn ht)
      rw [div_pow] at h
      convert h using 1
      ring
    · rw [if_neg ht, if_pos (lt_of_not_ge ht), zero_add]
      simpa only [div_eq_mul_inv, one_mul] using hsquare n B (hglobal n hn)
  calc
    _ ≤ ∑ n ∈ Icc 1 N,
        ((if T ≤ (N : ℝ) / n then
          A ^ 2 * ((1 / (n : ℝ)) / (1 + Real.log (((N : ℝ) / T) / n)) ^ 2) else 0) +
        (if (N : ℝ) / n < T then B ^ 2 * (1 / (n : ℝ)) else 0)) := sum_le_sum hpoint
    _ = A ^ 2 * (∑ n ∈ S, (1 / (n : ℝ)) /
          (1 + Real.log (((N : ℝ) / T) / n)) ^ 2) +
        B ^ 2 * (∑ n ∈ U, 1 / (n : ℝ)) := by
      rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← mul_sum, ← mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hkernel (sq_nonneg _))
      (mul_le_mul_of_nonneg_left (harmonic_quotient_tail_le hN hT) (sq_nonneg _))

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.harmonic_log_kernel_sum_le
#print axioms GaloisForLFunctions.HTGeometry.sum_sq_le_harmonic_log_envelope
