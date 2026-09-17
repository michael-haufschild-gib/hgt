import GaloisForLFunctions.RHTower.EulerDeletionLogPrimeForcing

/-!
# Exact logarithmic Abel history for compensated Euler deletion

The literal logarithmically weighted Möbius carrier is a terminal Möbius
carrier minus its entire logarithmic Abel history. Together with the exact
prime-dilation renewal, this retains the packet-forcing cancellation as one
signed vector. No norm estimate is taken here.
-/

noncomputable section
set_option autoImplicit false
open Finset
open scoped BigOperators

namespace RHTower.DeletionLogPrimeForcing

/-- Finite vector-valued Abel summation for the increasing logarithmic weight. -/
theorem logarithmic_abel_sum (f : ℕ → BDCarrier) (N : ℕ) :
    (∑ i ∈ range N, Real.log ((i : ℝ) + 1) • f i) =
      Real.log (N : ℝ) • (∑ i ∈ range N, f i) -
        ∑ i ∈ range (N-1),
          (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)) •
            (∑ j ∈ range (i+1), f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ (fun i => Real.log ((i : ℝ) + 1) • f i) N,
        Finset.sum_range_succ (fun i => f i) N]
      cases N with
      | zero => norm_num
      | succ N =>
          simp only [Nat.succ_sub_one, Finset.sum_range_succ, ih]
          push_cast
          have hlog : Real.log ((N : ℝ) + 1 + 1) = Real.log ((N : ℝ) + 2) := by
            congr 1
            ring
          rw [hlog]
          module

/-- The unweighted literal Möbius carrier used by the logarithmic history. -/
def mobiusSource (N : ℕ) : BDCarrier :=
  DeletionCoefficientTransfer.source
    (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N

/-- The logarithmic source is exactly its terminal Möbius vector minus every
earlier logarithmic Abel-history vector. -/
theorem logSource_eq_mobius_abel (N : ℕ) :
    logSource N =
      Real.log (N : ℝ) • mobiusSource N -
        ∑ i ∈ range (N-1),
          (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)) •
            mobiusSource (i+1) := by
  unfold logSource mobiusSource DeletionCoefficientTransfer.source
  have hleft :
      (∑ i ∈ range N,
        (((((ArithmeticFunction.moebius (i+1) : ℤ) : ℝ) *
          Real.log ((i+1 : ℕ) : ℝ)) : ℝ) : ℂ) •
          bdGen (1 / ((i : ℝ) + 1))) =
      ∑ i ∈ range N, Real.log ((i : ℝ) + 1) •
        (((ArithmeticFunction.moebius (i+1) : ℤ) : ℝ) : ℂ) •
          bdGen (1 / ((i : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hcast : ((i+1 : ℕ) : ℝ) = (i : ℝ) + 1 := by norm_num
    rw [hcast]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    module
  dsimp only
  change (∑ i ∈ range N,
      (((((ArithmeticFunction.moebius (i+1) : ℤ) : ℝ) *
        Real.log ((i+1 : ℕ) : ℝ)) : ℝ) : ℂ) •
        bdGen (1 / ((i : ℝ) + 1))) = _
  rw [hleft, logarithmic_abel_sum
    (f := fun i => (((ArithmeticFunction.moebius (i+1) : ℤ) : ℝ) : ℂ) •
      bdGen (1 / ((i : ℝ) + 1))) N]

end RHTower.DeletionLogPrimeForcing
