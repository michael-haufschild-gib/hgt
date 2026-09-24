import GaloisForLFunctions.RHTower.EulerDeletionCenteredLcmCoprimeConservation
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.Sieve.LowHeightMoebius

/-!
# Mertens-weighted inversion of physical lcm panels

The divisor-closed physical lcm sum is a coprime-discrepancy square. Möbius
inversion and finite hyperbola reindexing express an initial segment of lcm
grades as a signed Mertens-weighted sum of those exact panel squares.
This is an identity, not an upper bound on the EDQ signed carrier.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction

namespace RHTower

private theorem sum_Icc_moebius_eq_mertensM (k : ℕ) :
    (∑ j ∈ Icc 1 k, ((moebius j : ℤ) : ℝ)) = Sieve.mertensM k := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  rw [← Sieve.sum_range_moebius_shift_eq_mertensM k]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  exact congrArg moebius (Nat.add_comm 1 j)

private theorem sum_antidiagonal_swap (G : ℕ → ℝ) (n : ℕ) :
    (∑ x ∈ n.divisorsAntidiagonal, ((moebius x.1 : ℤ) : ℝ) * G x.2) =
      ∑ x ∈ n.divisorsAntidiagonal, G x.1 * ((moebius x.2 : ℤ) : ℝ) := by
  calc
    (∑ x ∈ n.divisorsAntidiagonal, ((moebius x.1 : ℤ) : ℝ) * G x.2) =
        ∑ d ∈ n.divisors, ((moebius (n / d) : ℤ) : ℝ) * G d := by
          exact Nat.sum_divisorsAntidiagonal'
            (fun a b => ((moebius a : ℤ) : ℝ) * G b)
    _ = ∑ d ∈ n.divisors, G d * ((moebius (n / d) : ℤ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact mul_comm _ _
    _ = ∑ x ∈ n.divisorsAntidiagonal, G x.1 * ((moebius x.2 : ℤ) : ℝ) := by
      exact (Nat.sum_divisorsAntidiagonal
        (fun a b => G a * ((moebius b : ℤ) : ℝ))).symm

/-- Finite divisor-panel inversion: a prefix of the Möbius inverse is a
Mertens-weighted sum of the original panel values. -/
theorem finite_divisor_panel_mertens_inversion
    (F G : ℕ → ℝ) (hpanel : ∀ n > 0, (∑ q ∈ n.divisors, F q) = G n)
    (N : ℕ) :
    (∑ q ∈ Icc 1 N, F q) =
      ∑ m ∈ Icc 1 N, Sieve.mertensM (N / m) * G m := by
  have hinv : ∀ n > 0,
      (∑ x ∈ n.divisorsAntidiagonal, (moebius x.1 : ℝ) * G x.2) = F n :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := F) (g := G)).mp hpanel
  calc
    (∑ q ∈ Icc 1 N, F q) =
        ∑ q ∈ Icc 1 N,
          ∑ x ∈ q.divisorsAntidiagonal, G x.1 * ((moebius x.2 : ℤ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [← hinv q (Finset.mem_Icc.mp hq).1, sum_antidiagonal_swap G q]
    _ = ∑ m ∈ Icc 1 N,
          ∑ k ∈ Icc 1 (N / m), G m * ((moebius k : ℤ) : ℝ) := by
            exact Sieve.sum_Icc_divisorsAntidiagonal_swap
              (fun m k => G m * ((moebius k : ℤ) : ℝ)) N
    _ = ∑ m ∈ Icc 1 N, Sieve.mertensM (N / m) * G m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [← Finset.mul_sum, sum_Icc_moebius_eq_mertensM]
      exact mul_comm _ _

/-- Every physical complete-grade prefix is a signed Mertens-weighted sum of
literal coprime-window discrepancy squares. No grade, physical weight, or
fixed-start coordinate has been replaced by a period average. -/
theorem physicalCenteredLcmFibre_initialSum_eq_mertensPanelSquares
    (N t H : ℕ) :
    (∑ q ∈ Icc 1 N, physicalCenteredLcmFibre q t H t H) =
      ∑ m ∈ Icc 1 N, Sieve.mertensM (N / m) *
        ((H : ℝ) * ((Nat.totient m : ℝ) / (m : ℝ)) -
          ((Ioc t (t + H)).filter (m.Coprime ·)).card) ^ (2 : ℕ) := by
  exact finite_divisor_panel_mertens_inversion
    (fun q => physicalCenteredLcmFibre q t H t H)
    (fun m => ((H : ℝ) * ((Nat.totient m : ℝ) / (m : ℝ)) -
      ((Ioc t (t + H)).filter (m.Coprime ·)).card) ^ (2 : ℕ))
    (fun n hn => physicalCenteredLcmFibre_divisorSum_eq_coprimeDiscrepancy_sq n t H hn)
    N

end RHTower
