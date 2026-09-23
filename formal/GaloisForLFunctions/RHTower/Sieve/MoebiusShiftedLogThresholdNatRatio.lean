import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogThreshold
import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogPrincipalExact

/-!
# Natural-ratio threshold forms of shifted Möbius kernels

These are the exact `X=N/q` specializations consumed after Selberg diagonalization.  They mirror
the corpus's unthresholded natural-ratio identities and centralize all floor/cast bookkeeping.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Thresholded linear Möbius kernel at the natural ratio `N/q`. -/
theorem sum_moebius_log_threshold_nat_ratio_eq_shifted
    (N q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ u ∈ Finset.Icc 1 (N / q),
      (selbergMoebiusReciprocalCoeff u *
        Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ))) *
          (if t ≤ Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) =
      moebiusShiftedLogKernelReal t
        (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) := by
  have h := sum_moebius_log_threshold_eq_shifted
    ((N : ℝ) / (q : ℝ)) t (by positivity) ht
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro u hu
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have huR : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1)
  have harg : (N : ℝ) / (q : ℝ) / (u : ℝ) =
      (N : ℝ) / ((q * u : ℕ) : ℝ) := by
    push_cast
    field_simp [hqR, huR]
  rw [selbergMoebiusReciprocalCoeff, harg]

/-- Thresholded quadratic Möbius kernel at the natural ratio `N/q`. -/
theorem sum_moebius_log_sq_threshold_nat_ratio_eq_shifted
    (N q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ u ∈ Finset.Icc 1 (N / q),
      (selbergMoebiusReciprocalCoeff u *
        Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) ^ (2 : ℕ)) *
          (if t ≤ Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) =
      moebiusShiftedLogSqKernelReal t
        (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) := by
  have h := sum_moebius_log_sq_threshold_eq_shifted
    ((N : ℝ) / (q : ℝ)) t (by positivity) ht
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro u hu
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have huR : (u : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1)
  have harg : (N : ℝ) / (q : ℝ) / (u : ℝ) =
      (N : ℝ) / ((q * u : ℕ) : ℝ) := by
    push_cast
    field_simp [hqR, huR]
  rw [selbergMoebiusReciprocalCoeff, harg]

end

end RHTower.Sieve
