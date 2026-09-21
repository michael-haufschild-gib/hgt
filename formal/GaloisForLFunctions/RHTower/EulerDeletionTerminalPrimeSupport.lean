import GaloisForLFunctions.RHTower.EulerDeletionChildFibreContrast

/-!
# Prime support of terminal Euler-deletion child energy

At a terminal EDQ refinement, every non-prime level has zero physical child
contrast.  The two mechanisms are disjoint and exact: a non-prime-power
successor is already periodic on the preceding clock, whereas a proper prime
power has vanishing Möbius coefficient.  Thus the terminal contrast carrier is
strictly smaller than the previously available prime-power clock-jump carrier.
-/

noncomputable section
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

private theorem physical_moebius_cell_eq_zero_of_clock_dvd (N k : ℕ)
    (hk : clock N ∣ k) :
    DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) N k = 0 := by
  rw [DeletionCoefficientTransfer.cell]
  apply Finset.sum_eq_zero
  intro i hi
  have hiN : i < N := Finset.mem_range.mp hi
  have hid : i + 1 ∣ clock N :=
    dvd_clock (Nat.succ_pos i) (Nat.succ_le_of_lt hiN)
  rw [Nat.mod_eq_zero_of_dvd (hid.trans hk)]
  simp

private theorem moebius_succ_eq_zero_of_isPrimePow_not_prime (n : ℕ)
    (hpp : IsPrimePow (n + 1)) (hn : ¬ (n + 1).Prime) :
    moebius (n + 1) = 0 := by
  obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff _).mp hpp
  have hk1 : k ≠ 1 := by
    intro he
    apply hn
    rw [← hpow, he]
    simpa using hp
  rw [← hpow, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg hk1]

/-- Every literal terminal physical Möbius cell at a non-prime level vanishes.
The result preserves the physical endpoint and does not average child offsets. -/
theorem terminal_physical_moebius_cell_eq_zero_of_not_prime (n b : ℕ)
    (hn : ¬ (n + 1).Prime) :
    DeletionCoefficientTransfer.cell (fun d => ((moebius d : ℤ) : ℝ)) (n + 1)
      (clock n * (b + 1)) = 0 := by
  by_cases hpp : IsPrimePow (n + 1)
  · have hmu : moebius (n + 1) = 0 :=
      moebius_succ_eq_zero_of_isPrimePow_not_prime n hpp hn
    rw [physical_moebius_cell_block n 1 (clock n * (b + 1))]
    simp [physical_moebius_cell_eq_zero_of_clock_dvd,
      dvd_mul_right (clock n) (b + 1), hmu]
  · apply physical_moebius_cell_eq_zero_of_clock_dvd
    rw [clock_succ_eq_of_dvd n (successor_dvd_clock_of_not_isPrimePow n hpp)]
    exact dvd_mul_right _ _

/-- The beta-weighted terminal source tail is zero at each non-prime level.
This is an exact source identity, not a bound on its absolute value. -/
theorem intervalIntegral_terminalChildTailKernel_eq_zero_of_not_prime
    (n b : ℕ) (hn : ¬ (n + 1).Prime)
    (hb : b < clock (n + 1) / clock n) :
    (∫ x in (0 : ℝ)..1, terminalChildTailKernel n b x) = 0 := by
  rw [intervalIntegral_terminalChildTailKernel_eq_physicalCell_weight n b hb,
    terminal_physical_moebius_cell_eq_zero_of_not_prime n b hn]
  simp

/-- Every pair of terminal child values agrees at a non-prime level. -/
theorem terminal_historyLayer_child_difference_eq_zero_of_not_prime
    (n b c : ℕ) (hn : ¬ (n + 1).Prime)
    (hb : b < clock (n + 1) / clock n)
    (hc : c < clock (n + 1) / clock n) :
    historyLayer n (predictableDrift (n + 1)) (clock n - 1 + b * clock n) -
      historyLayer n (predictableDrift (n + 1)) (clock n - 1 + c * clock n) = 0 := by
  rw [terminal_historyLayer_child_difference_eq_physicalCell_of_not_prime n b c hn hb hc,
    terminal_physical_moebius_cell_eq_zero_of_not_prime n b hn,
    terminal_physical_moebius_cell_eq_zero_of_not_prime n c hn]
  simp

/-- The exact terminal EDQ child energy is supported on primes, not merely
prime powers.  No term in the pairwise physical quadratic form is discarded. -/
theorem two_mul_terminal_historyLayer_parent_child_energy_eq_zero_of_not_prime
    (n : ℕ) (hn : ¬ (n + 1).Prime) :
    2 * cellMeasure.real (historyFibre n (clock n - 1)) *
        (∑ b ∈ range (clock (n + 1) / clock n),
          cellMeasure.real (historyFibre (n + 1) (clock n - 1 + b * clock n)) *
            (historyLayer n (predictableDrift (n + 1)) (clock n - 1 + b * clock n)) ^ 2) = 0 := by
  rw [two_mul_terminal_historyLayer_parent_child_energy_eq_physicalCell_pairwise]
  apply Finset.sum_eq_zero
  intro b hb
  apply Finset.sum_eq_zero
  intro c hc
  have hinnovb : signedInnovation n (clock n - 1 + b * clock n) = 0 := by
    exact cell_point_eq_of_ae (f := fun k => signedInnovation n k)
      (g := fun _ => 0) (by
        rw [signedInnovation_eq_zero_of_not_prime n hn]
        exact Lp.coeFn_zero ℝ 2 cellMeasure) _
  have hinnovc : signedInnovation n (clock n - 1 + c * clock n) = 0 := by
    exact cell_point_eq_of_ae (f := fun k => signedInnovation n k)
      (g := fun _ => 0) (by
        rw [signedInnovation_eq_zero_of_not_prime n hn]
        exact Lp.coeFn_zero ℝ 2 cellMeasure) _
  rw [terminal_physical_moebius_cell_eq_zero_of_not_prime n b hn,
    terminal_physical_moebius_cell_eq_zero_of_not_prime n c hn, hinnovb, hinnovc]
  ring

end RHTower.DeletionResidueMartingale
