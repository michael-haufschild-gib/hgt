import GaloisForLFunctions.RHTower.CCMFUSuzukiSelbergOutgoingAbelWeld
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier

/-!
# Exact tail bridge from the SP-E source to the Weil lag

The completed SP-E source is the prefix half-order Abel action of the discrete Chebyshev
remainder.  The integer Weil lag has a different orientation: after its endpoint error cancels
against the Mertens deviation, it is a tail transform of the same Chebyshev error.  This file
closes the local, source-faithful bridge between those two orientations.

The cell identity is exact.  It reconstructs each `psiRemainder k` from the difference of two
successive Weil-lag tails and explicit logarithmic terms.  It does not assert the global signed
moderation required by SP-E; that remaining step must control the resulting boundary and weighted
interior lag terms without taking absolute values before cancellation.
-/

open MeasureTheory Set Filter Topology
open scoped Chebyshev
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-- The Chebyshev-error tail read by the integer Weil lag. -/
def weilLagChebyshevTail (n : ℕ) : ℝ :=
  ∫ t in Set.Ioi (n : ℝ), chebyshevError t / t ^ (2 : ℕ)

/-- The endpoint Chebyshev error cancels exactly in the integer Weil lag, leaving its tail. -/
theorem sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch
    (n : ℕ) (hn : 2 ≤ n) :
    Real.sqrt n * integerLag n =
      -(n : ℝ) * weilLagChebyshevTail n -
        Real.log (2 * Real.pi) + trivialZeroSeriesReal n := by
  rw [integerLag_eq hn]
  unfold weilLagChebyshevTail
  have h := mertensDeviation_eq (x := (n : ℝ))
    (by exact_mod_cast (by omega : 1 ≤ n))
  norm_num only [Nat.floor_natCast] at h
  rw [← mertensSum_eq_Icc_zero] at h
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hmul := congrArg (fun x : ℝ => (n : ℝ) * x) h
  field_simp [hn0] at hmul
  simp only [chebyshevError] at hmul
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have hcancel : Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ))⁻¹ = 1 := by
    field_simp [hsqrt]
  rw [one_div, ← mul_assoc, hcancel, one_mul]
  unfold chebyshevError
  linarith only [hmul]

/-- Exact one-step increment of the Mertens sum. -/
theorem mertensSum_succ_sub_eq_vonMangoldt_div (k : ℕ) :
    mertensSum (k + 1) - mertensSum k =
      vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  unfold mertensSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
  ring

/-- Reverse finite summation by parts for a tail difference. -/
theorem sum_mul_tail_sub_telescope (a T : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 1 (N + 1), a k * (T k - T (k + 1))) =
      a 1 * T 1 - a (N + 1) * T (N + 2) +
        ∑ k ∈ Finset.Icc 2 (N + 1), (a k - a (k - 1)) * T k := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 2), ih,
        Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 2)]
      simp only [Nat.add_sub_cancel]
      ring

/-- A discrete difference of successive Weil-lag tails reconstructs the exact SP-E source cell. -/
theorem psiRemainder_eq_weilLagChebyshevTail_difference (k : ℕ) (hk : 1 ≤ k) :
    psiRemainder k = (k : ℝ) * (k + 1 : ℕ) *
      (weilLagChebyshevTail k - weilLagChebyshevTail (k + 1) +
        Real.log ((k + 1 : ℕ) : ℝ) - Real.log k - 1 / ((k + 1 : ℕ) : ℝ)) := by
  have hK := mertensDeviation_eq (x := (k : ℝ)) (by exact_mod_cast hk)
  have hK1 := mertensDeviation_eq (x := ((k + 1 : ℕ) : ℝ))
    (by exact_mod_cast (by omega : 1 ≤ k + 1))
  norm_num only [Nat.floor_natCast] at hK hK1
  rw [← mertensSum_eq_Icc_zero] at hK hK1
  rw [chebyshevError] at hK hK1
  have hM := mertensSum_succ_sub_eq_vonMangoldt_div k
  have hE := psiRemainder_succ_sub k
  unfold weilLagChebyshevTail
  simp only [psiRemainder, chebyshevPsi_eq_psi] at hE ⊢
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < k))
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hsource :
      Chebyshev.psi ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) =
        (Chebyshev.psi (k : ℝ) - (k : ℝ)) + vonMangoldt (k + 1) - 1 := by
    linarith only [hE]
  have hmertens :
      (mertensSum (k + 1) - Real.log ((k + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant) -
          (mertensSum k - Real.log (k : ℝ) + Real.eulerMascheroniConstant) =
        vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) -
          Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k : ℝ) := by
    calc
      _ = (mertensSum (k + 1) - mertensSum k) -
          Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k : ℝ) := by ring
      _ = _ := by rw [hM]
  have htail :
      (mertensSum (k + 1) - Real.log ((k + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant) -
          (mertensSum k - Real.log (k : ℝ) + Real.eulerMascheroniConstant) =
        vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) -
          (Chebyshev.psi (k : ℝ) - (k : ℝ)) / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) +
          (∫ t in Set.Ioi (k : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
            (∫ t in Set.Ioi ((k + 1 : ℕ) : ℝ), chebyshevError t / t ^ (2 : ℕ)) := by
    rw [hK, hK1, hsource]
    field_simp [hk0, hk1]
    push_cast
    ring
  have htailEq :
      (Chebyshev.psi (k : ℝ) - (k : ℝ)) / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) =
        (∫ t in Set.Ioi (k : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
          (∫ t in Set.Ioi ((k + 1 : ℕ) : ℝ), chebyshevError t / t ^ (2 : ℕ)) +
            Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
    have hEq :
        vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) -
            Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k : ℝ) =
          vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) -
            (Chebyshev.psi (k : ℝ) - (k : ℝ)) / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) +
              (∫ t in Set.Ioi (k : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
                (∫ t in Set.Ioi ((k + 1 : ℕ) : ℝ), chebyshevError t / t ^ (2 : ℕ)) :=
      hmertens.symm.trans htail
    have hsum :
        (Chebyshev.psi (k : ℝ) - (k : ℝ)) / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) +
            (vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) -
              Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k : ℝ)) =
          vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) +
            (∫ t in Set.Ioi (k : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
              (∫ t in Set.Ioi ((k + 1 : ℕ) : ℝ), chebyshevError t / t ^ (2 : ℕ)) := by
      rw [hEq]
      ring
    have hsolve :
        (Chebyshev.psi (k : ℝ) - (k : ℝ)) / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) =
          (vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) +
            (∫ t in Set.Ioi (k : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
              (∫ t in Set.Ioi ((k + 1 : ℕ) : ℝ), chebyshevError t / t ^ (2 : ℕ))) -
            (vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) -
              Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k : ℝ)) :=
      (eq_sub_iff_add_eq).mpr hsum
    calc
      _ = (vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) +
            (∫ t in Set.Ioi (k : ℝ), chebyshevError t / t ^ (2 : ℕ)) -
              (∫ t in Set.Ioi ((k + 1 : ℕ) : ℝ), chebyshevError t / t ^ (2 : ℕ))) -
          (vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) -
            Real.log ((k + 1 : ℕ) : ℝ) + Real.log (k : ℝ)) := hsolve
      _ = _ := by ring
  have hprod : (k : ℝ) * ((k + 1 : ℕ) : ℝ) ≠ 0 := mul_ne_zero hk0 hk1
  calc
    Chebyshev.psi (k : ℝ) - (k : ℝ) =
        ((Chebyshev.psi (k : ℝ) - (k : ℝ)) /
          ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) * ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
      exact (div_mul_cancel₀ _ hprod).symm
    _ = _ := by
      rw [htailEq]
      push_cast
      ring

/-- Coefficient multiplying one successive Weil-lag-tail difference. -/
def weilLagTailCellWeight (k : ℕ) : ℝ :=
  (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * (k : ℝ) * ((k + 1 : ℕ) : ℝ)

/-- The explicit elementary part of one tail-reconstructed SP-E cell. -/
def weilLagTailArchCell (k : ℕ) : ℝ :=
  weilLagTailCellWeight k *
    (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))

/-- Exact finite Green identity from the SP-E prefix action to Weil-lag tails.

The right hand side retains both tail boundaries and the signed interior tail mean. -/
theorem coherentSelbergSquareRootAbelMoment_eq_weilLagTail_green (N : ℕ) :
    coherentSelbergSquareRootAbelMoment (N + 2) =
      weilLagTailCellWeight 1 * weilLagChebyshevTail 1 -
        weilLagTailCellWeight (N + 1) * weilLagChebyshevTail (N + 2) +
          ∑ k ∈ Finset.Icc 2 (N + 1),
            (weilLagTailCellWeight k - weilLagTailCellWeight (k - 1)) *
              weilLagChebyshevTail k +
          ∑ k ∈ Finset.Icc 1 (N + 1), weilLagTailArchCell k := by
  rw [coherentSelbergSquareRootAbelMoment]
  rw [show N + 2 - 1 = N + 1 by omega]
  calc
    _ = ∑ k ∈ Finset.Icc 1 (N + 1),
        (weilLagTailCellWeight k *
          (weilLagChebyshevTail k - weilLagChebyshevTail (k + 1)) +
            weilLagTailArchCell k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [psiRemainder_eq_weilLagChebyshevTail_difference k hk1]
      simp only [weilLagTailArchCell, weilLagTailCellWeight]
      ring
    _ = (∑ k ∈ Finset.Icc 1 (N + 1),
          weilLagTailCellWeight k *
            (weilLagChebyshevTail k - weilLagChebyshevTail (k + 1))) +
          ∑ k ∈ Finset.Icc 1 (N + 1), weilLagTailArchCell k := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_mul_tail_sub_telescope]

/-- The integer-lag numerator of a Chebyshev-error tail after endpoint cancellation. -/
def weilLagTailIntegerNumerator (n : ℕ) : ℝ :=
  -Real.sqrt n * integerLag n - Real.log (2 * Real.pi) + trivialZeroSeriesReal n

/-- The tail read by the integer lag, with its natural integer-scale normalization restored. -/
theorem natCast_mul_weilLagChebyshevTail_eq_integerNumerator
    (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * weilLagChebyshevTail n = weilLagTailIntegerNumerator n := by
  rw [weilLagTailIntegerNumerator]
  have h := sqrt_mul_integerLag_eq_neg_mul_weilLagChebyshevTail_add_arch n hn
  linarith only [h]

/-- Exact integer-lag expression for every Chebyshev-error tail at integer scale at least two. -/
theorem weilLagChebyshevTail_eq_integerNumerator_div
    (n : ℕ) (hn : 2 ≤ n) :
    weilLagChebyshevTail n = weilLagTailIntegerNumerator n / n := by
  apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).mpr
  rw [mul_comm]
  exact natCast_mul_weilLagChebyshevTail_eq_integerNumerator n hn

/-- Exact source-to-integer-lag Green identity for the completed SP-E Abel action.

It retains the terminal lag and the signed interior lag mean, so it is an identity rather than a
bound on either term. -/
theorem coherentSelbergSquareRootAbelMoment_eq_integerLag_green (N : ℕ) :
    coherentSelbergSquareRootAbelMoment (N + 2) =
      weilLagTailCellWeight 1 * weilLagChebyshevTail 1 -
        weilLagTailCellWeight (N + 1) *
          (weilLagTailIntegerNumerator (N + 2) / ((N + 2 : ℕ) : ℝ)) +
          ∑ k ∈ Finset.Icc 2 (N + 1),
            (weilLagTailCellWeight k - weilLagTailCellWeight (k - 1)) *
              (weilLagTailIntegerNumerator k / (k : ℝ)) +
          ∑ k ∈ Finset.Icc 1 (N + 1), weilLagTailArchCell k := by
  rw [coherentSelbergSquareRootAbelMoment_eq_weilLagTail_green]
  have htop : weilLagChebyshevTail (N + 2) =
      weilLagTailIntegerNumerator (N + 2) / ((N + 2 : ℕ) : ℝ) :=
    weilLagChebyshevTail_eq_integerNumerator_div (N + 2) (by omega)
  have hinterior :
      (∑ k ∈ Finset.Icc 2 (N + 1),
        (weilLagTailCellWeight k - weilLagTailCellWeight (k - 1)) *
          weilLagChebyshevTail k) =
        ∑ k ∈ Finset.Icc 2 (N + 1),
          (weilLagTailCellWeight k - weilLagTailCellWeight (k - 1)) *
            (weilLagTailIntegerNumerator k / (k : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [weilLagChebyshevTail_eq_integerNumerator_div k (Finset.mem_Icc.mp hk).1]
  rw [htop]
  rw [hinterior]

end

end RHTower
