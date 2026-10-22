import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# Terminal Chebyshev reduction of the CCM--FU factorial prefix

The critical delayed prime--polar coefficient has a finite factorial primitive.  This file
identifies its literal prefix without a bound or an RH premise: it is the terminal Chebyshev
remainder plus a completely deterministic factorial boundary.  Thus factorial cancellation does
not remove the arithmetic obstruction; it transports it to one endpoint.
-/

open scoped BigOperators

namespace RHTower

open ArithmeticFunction Finset

noncomputable section

private theorem ccmFUSuzuki_sum_Icc_vonMangoldt_eq_psi (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, ArithmeticFunction.vonMangoldt n =
      Chebyshev.psi (X : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro n _
    rfl

/-- Source-free factorial boundary left after the critical shifted prime--polar prefix is
compared to its terminal Chebyshev remainder. -/
def ccmFUSuzukiCriticalFactorialEndpointDefect (N : ℕ) : ℝ :=
  ((N + 3 : ℕ) : ℝ) - ((N + 3 : ℕ) : ℝ) * Real.log ((N + 3 : ℕ) : ℝ) +
    Real.log (((N + 2).factorial : ℕ) : ℝ) + Real.log 2

private theorem ccmFUSuzuki_shifted_sum_vonMangoldt (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt (j + 3)) =
      psiRemainder (N + 3) + ((N + 3 : ℕ) : ℝ) - Real.log 2 := by
  rw [Finset.range_eq_Ico]
  have hshift := Finset.sum_Ico_add (fun k : ℕ => ArithmeticFunction.vonMangoldt k)
    0 (N + 1) 3
  have hshift' :
      (∑ j ∈ Finset.Ico 0 (N + 1), ArithmeticFunction.vonMangoldt (j + 3)) =
        ∑ k ∈ Finset.Ico 3 (N + 3 + 1), ArithmeticFunction.vonMangoldt k := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift
  rw [hshift']
  rw [show Finset.Ico 3 (N + 3 + 1) = Finset.Icc 3 (N + 3) by
    ext k
    simp]
  have hsplit :
      (∑ k ∈ Finset.Icc 1 (N + 3), ArithmeticFunction.vonMangoldt k) =
        ArithmeticFunction.vonMangoldt 1 + ArithmeticFunction.vonMangoldt 2 +
          ∑ k ∈ Finset.Icc 3 (N + 3), ArithmeticFunction.vonMangoldt k := by
    rw [show Finset.Icc 1 (N + 3) = insert 1 (insert 2 (Finset.Icc 3 (N + 3))) by
      ext k
      simp
      omega]
    simp [ArithmeticFunction.vonMangoldt_apply_one,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rw [ccmFUSuzuki_sum_Icc_vonMangoldt_eq_psi] at hsplit
  rw [psiRemainder, chebyshevPsi_eq_psi]
  norm_num [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at hsplit
  push_cast at hsplit ⊢
  linarith

private theorem ccmFUSuzuki_shifted_weighted_logRatio (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      ((j + 3 : ℕ) : ℝ) *
        (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ))) =
      ((N + 3 : ℕ) : ℝ) * Real.log ((N + 3 : ℕ) : ℝ) -
        Real.log (((N + 2).factorial : ℕ) : ℝ) - 2 * Real.log 2 := by
  induction N with
  | zero => norm_num; ring_nf
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hN3 : ((N + 3 : ℕ) : ℝ) ≠ 0 := by positivity
      have hfact : (((N + 3).factorial : ℕ) : ℝ) =
          ((N + 3 : ℕ) : ℝ) * (((N + 2).factorial : ℕ) : ℝ) := by
        norm_cast
      have hfactne : (((N + 2).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      rw [hfact, Real.log_mul hN3 hfactne]
      push_cast
      ring

/-- **Terminal source law.** The literal finite critical coefficient prefix is the terminal
Chebyshev remainder plus its deterministic factorial boundary.  In particular, no cancellation
argument based only on the factorial primitive can erase the terminal arithmetic source. -/
theorem ccmFUSuzuki_shiftedPrimePolarFactorial_eq_psiRemainder_add_endpointDefect (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
      (ArithmeticFunction.vonMangoldt (j + 3) -
        ((j + 3 : ℕ) : ℝ) *
          (Real.log ((j + 3 : ℕ) : ℝ) - Real.log ((j + 2 : ℕ) : ℝ)))) =
      psiRemainder (N + 3) + ccmFUSuzukiCriticalFactorialEndpointDefect N := by
  rw [Finset.sum_sub_distrib, ccmFUSuzuki_shifted_sum_vonMangoldt,
    ccmFUSuzuki_shifted_weighted_logRatio,
    ccmFUSuzukiCriticalFactorialEndpointDefect]
  ring

end

end RHTower
