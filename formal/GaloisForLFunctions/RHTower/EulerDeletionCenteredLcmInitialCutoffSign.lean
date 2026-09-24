import GaloisForLFunctions.RHTower.EulerDeletionCenteredLcmCoprimeConservation
import GaloisForLFunctions.RHTower.EulerDeletionCenteredLcmSemiprimeSign

/-!
# Physical complete-lcm cutoff can have negative sign

The positive divisor-closed conservation law does not extend to a physical
initial segment of complete lcm grades. The counterexample uses the literal
Möbius-weighted window discrepancy, not arbitrary coefficient vectors.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction

namespace RHTower

private theorem physical_lcm_zero_of_mu_zero
    (q t H : ℕ) (hq : 0 < q) (hmu : moebius q = (0 : ℤ)) :
    physicalCenteredLcmFibre q t H t H = 0 := by
  rw [physicalCenteredLcmFibre_eq_doubleCentered_windows q t H t H hq]
  simp_rw [centeredLcmFibre_eq_doubleCentered_productIncidence]
  simp [hmu]

private theorem window15_discrepancy (d : ℕ) :
    DeletionResidueMartingale.divisorWindowDiscrepancy d 0 15 =
      (15 : ℝ) / (d : ℝ) - ((15 / d : ℕ) : ℝ) := by
  unfold DeletionResidueMartingale.divisorWindowDiscrepancy
  simp only [Nat.zero_add, Nat.Ioc_filter_dvd_card_eq_div]
  rfl

private theorem window15_d2 :
    DeletionResidueMartingale.divisorWindowDiscrepancy 2 0 15 = 1 / 2 := by
  rw [window15_discrepancy]
  norm_num

private theorem window15_d3 :
    DeletionResidueMartingale.divisorWindowDiscrepancy 3 0 15 = 0 := by
  rw [window15_discrepancy]
  norm_num

private theorem window15_d5 :
    DeletionResidueMartingale.divisorWindowDiscrepancy 5 0 15 = 0 := by
  rw [window15_discrepancy]
  norm_num

private theorem window15_d6 :
    DeletionResidueMartingale.divisorWindowDiscrepancy 6 0 15 = 1 / 2 := by
  rw [window15_discrepancy]
  norm_num

private theorem window15_d7 :
    DeletionResidueMartingale.divisorWindowDiscrepancy 7 0 15 = 1 / 7 := by
  rw [window15_discrepancy]
  norm_num

private theorem window15_d10 :
    DeletionResidueMartingale.divisorWindowDiscrepancy 10 0 15 = 1 / 2 := by
  rw [window15_discrepancy]
  norm_num

private theorem window15_fibre1 : physicalCenteredLcmFibre 1 0 15 0 15 = 0 := by
  have hone : DeletionResidueMartingale.divisorWindowDiscrepancy 1 0 15 = 0 :=
    DeletionResidueMartingale.divisorWindowDiscrepancy_eq_zero_of_dvd
      1 0 15 (by omega) (one_dvd 15)
  have h := physicalCenteredLcmFibre_divisorSum_eq_square 1 0 15 (by omega)
  simpa [hone] using h

private theorem window15_fibre2 : physicalCenteredLcmFibre 2 0 15 0 15 = 1 / 4 := by
  rw [physicalCenteredLcmFibre_prime_eq_square 2 0 15 Nat.prime_two,
    window15_d2]
  norm_num

private theorem window15_fibre5 : physicalCenteredLcmFibre 5 0 15 0 15 = 0 := by
  rw [physicalCenteredLcmFibre_prime_eq_square 5 0 15 Nat.prime_five,
    window15_d5]
  norm_num

private theorem window15_fibre10 : physicalCenteredLcmFibre 10 0 15 0 15 = -(1 / 4 : ℝ) := by
  have h := physicalCenteredLcmFibre_semiprime_eq
    Nat.prime_two Nat.prime_five (by omega : 2 ≠ 5) 0 15
  norm_num only at h
  rw [h]
  simp only [window15_d2, window15_d5, window15_d10]
  norm_num

private theorem window15_fibre6 : physicalCenteredLcmFibre 6 0 15 0 15 = -(1 / 4 : ℝ) := by
  have h := physicalCenteredLcmFibre_semiprime_eq
    Nat.prime_two Nat.prime_three (by omega : 2 ≠ 3) 0 15
  norm_num only at h
  rw [h]
  simp only [window15_d2, window15_d3, window15_d6]
  norm_num

private theorem window15_fibre7 : physicalCenteredLcmFibre 7 0 15 0 15 = 1 / 49 := by
  rw [physicalCenteredLcmFibre_prime_eq_square 7 0 15 Nat.prime_seven,
    window15_d7]
  norm_num

private theorem window15_fibre3 : physicalCenteredLcmFibre 3 0 15 0 15 = 0 := by
  rw [physicalCenteredLcmFibre_prime_eq_square 3 0 15 Nat.prime_three,
    window15_d3]
  norm_num

private theorem window15_fibre4 : physicalCenteredLcmFibre 4 0 15 0 15 = 0 := by
  apply physical_lcm_zero_of_mu_zero 4 0 15 (by omega)
  have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
    (show (2 : ℕ) ≠ 0 by omega)
  norm_num at h
  exact h

private theorem window15_fibre8 : physicalCenteredLcmFibre 8 0 15 0 15 = 0 := by
  apply physical_lcm_zero_of_mu_zero 8 0 15 (by omega)
  have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
    (show (3 : ℕ) ≠ 0 by omega)
  norm_num at h
  exact h

private theorem window15_fibre9 : physicalCenteredLcmFibre 9 0 15 0 15 = 0 := by
  apply physical_lcm_zero_of_mu_zero 9 0 15 (by omega)
  have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_three
    (show (2 : ℕ) ≠ 0 by omega)
  norm_num at h
  exact h

/-- The actual signed complete-grade prefix can be negative, even though
every divisor-closed subpanel is a nonnegative discrepancy square. -/
theorem physicalCenteredLcmFibre_initialTen_window15_eq :
    (∑ q ∈ Icc 1 10, physicalCenteredLcmFibre q 0 15 0 15) = -(45 / 196 : ℝ) := by
  have hset : Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) := by decide
  rw [hset]
  simp [window15_fibre1, window15_fibre2, window15_fibre3, window15_fibre4,
    window15_fibre5, window15_fibre6, window15_fibre7, window15_fibre8,
    window15_fibre9, window15_fibre10]
  norm_num

theorem physicalCenteredLcmFibre_initialTen_window15_neg :
    (∑ q ∈ Icc 1 10, physicalCenteredLcmFibre q 0 15 0 15) < 0 := by
  rw [physicalCenteredLcmFibre_initialTen_window15_eq]
  norm_num

end RHTower
