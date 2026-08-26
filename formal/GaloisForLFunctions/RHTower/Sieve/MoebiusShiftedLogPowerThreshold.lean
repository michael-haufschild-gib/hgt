import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogPowerRealCutoff
import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogThreshold
import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogPrincipalExact

/-!
# Threshold forms of arbitrary shifted Möbius kernels

The logarithmic layer condition cuts an arbitrary positive log-power kernel at
`X * exp (-t)`.  This removes the former degree-one/degree-two restriction from the exact
minimum-logarithmic Selberg interface.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- A thresholded arbitrary logarithmic-power Möbius sum is its shifted kernel. -/
theorem sum_moebius_log_pow_threshold_eq_shifted
    (p : ℕ) (X t : ℝ) (hX : 0 < X) (ht : 0 ≤ t) :
    (∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
      (((moebius d : ℤ) : ℝ) / (d : ℝ) *
        Real.log (X / (d : ℝ)) ^ p) *
          (if t ≤ Real.log (X / (d : ℝ)) then (1 : ℝ) else 0)) =
      moebiusShiftedLogPowerKernelReal p t (X * Real.exp (-t)) := by
  let S := Finset.Icc 1 ⌊X⌋₊
  let T := Finset.Icc 1 ⌊X * Real.exp (-t)⌋₊
  have hfilter : S.filter (fun d : ℕ => t ≤ Real.log (X / (d : ℝ))) = T := by
    ext d
    simp only [S, T, Finset.mem_filter]
    constructor
    · rintro ⟨hdS, hdt⟩
      exact (mem_Icc_floor_mul_exp_neg_iff hX ht
        (Finset.mem_Icc.mp hdS).1).mpr ⟨hdS, hdt⟩
    · intro hdT
      exact (mem_Icc_floor_mul_exp_neg_iff hX ht
        (Finset.mem_Icc.mp hdT).1).mp hdT
  rw [show (∑ d ∈ S,
      (((moebius d : ℤ) : ℝ) / (d : ℝ) *
        Real.log (X / (d : ℝ)) ^ p) *
          (if t ≤ Real.log (X / (d : ℝ)) then (1 : ℝ) else 0)) =
      ∑ d ∈ S.filter (fun d : ℕ => t ≤ Real.log (X / (d : ℝ))),
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (X / (d : ℝ)) ^ p by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdt : t ≤ Real.log (X / (d : ℝ)) <;> simp [hdt]]
  rw [hfilter, moebiusShiftedLogPowerKernelReal]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hlog : t + Real.log ((X * Real.exp (-t)) / (d : ℝ)) =
      Real.log (X / (d : ℝ)) := by
    rw [Real.log_div (mul_ne_zero hX.ne' (Real.exp_ne_zero (-t))) hdR.ne',
      Real.log_mul hX.ne' (Real.exp_ne_zero (-t)), Real.log_exp,
      Real.log_div hX.ne' hdR.ne']
    ring
  rw [hlog]

/-- Natural-ratio specialization of the arbitrary-power threshold identity. -/
theorem sum_moebius_log_pow_threshold_nat_ratio_eq_shifted
    (p N q : ℕ) (hN : 0 < N) (hq : 0 < q)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ u ∈ Finset.Icc 1 (N / q),
      (selbergMoebiusReciprocalCoeff u *
        Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) ^ p) *
          (if t ≤ Real.log ((N : ℝ) / ((q * u : ℕ) : ℝ)) then
            (1 : ℝ) else 0)) =
      moebiusShiftedLogPowerKernelReal p t
        (((N : ℝ) / (q : ℝ)) * Real.exp (-t)) := by
  have h := sum_moebius_log_pow_threshold_eq_shifted
    p ((N : ℝ) / (q : ℝ)) t (by positivity) ht
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
