import GaloisForLFunctions.RHTower.Sieve.MoebiusShiftedLogRealCutoff
import GaloisForLFunctions.RHTower.LogFloorExpBridge

/-!
# Logarithmic threshold form of shifted Möbius kernels

The cutoff `d ≤ X exp(-t)` is exactly the layer condition `t ≤ log(X/d)`.  These identities
reindex thresholded linear and quadratic logarithmic Möbius sums onto the affine-shift kernels.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Natural-floor cutoff at `X exp(-t)` equals the logarithmic layer inside the cutoff at `X`. -/
theorem mem_Icc_floor_mul_exp_neg_iff
    {X t : ℝ} (hX : 0 < X) (ht : 0 ≤ t)
    {d : ℕ} (hd : 1 ≤ d) :
    d ∈ Finset.Icc 1 ⌊X * Real.exp (-t)⌋₊ ↔
      d ∈ Finset.Icc 1 ⌊X⌋₊ ∧ t ≤ Real.log (X / (d : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hexp : Real.exp (Real.log X - t) = X * Real.exp (-t) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hX]
  have hcutle : X * Real.exp (-t) ≤ X := by
    have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-t)]
  constructor
  · intro hmem
    have hdc : d ≤ ⌊X * Real.exp (-t)⌋₊ := (Finset.mem_Icc.mp hmem).2
    have hdX : d ≤ ⌊X⌋₊ := hdc.trans (Nat.floor_le_floor hcutle)
    have hlog : Real.log d ≤ Real.log X - t := by
      apply (RHTower.log_le_iff_le_floor hd (Real.log X - t)).mpr
      rwa [hexp]
    refine ⟨Finset.mem_Icc.mpr ⟨hd, hdX⟩, ?_⟩
    rw [Real.log_div hX.ne' hdR.ne']
    linarith
  · rintro ⟨-, hthreshold⟩
    have hlog : Real.log d ≤ Real.log X - t := by
      rw [Real.log_div hX.ne' hdR.ne'] at hthreshold
      linarith
    have hdc : d ≤ ⌊Real.exp (Real.log X - t)⌋₊ :=
      (RHTower.log_le_iff_le_floor hd (Real.log X - t)).mp hlog
    rw [hexp] at hdc
    exact Finset.mem_Icc.mpr ⟨hd, hdc⟩

/-- A thresholded linear logarithmic Möbius sum is the shifted linear kernel. -/
theorem sum_moebius_log_threshold_eq_shifted
    (X t : ℝ) (hX : 0 < X) (ht : 0 ≤ t) :
    (∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
      (((moebius d : ℤ) : ℝ) / (d : ℝ) *
        Real.log (X / (d : ℝ))) *
          (if t ≤ Real.log (X / (d : ℝ)) then (1 : ℝ) else 0)) =
      moebiusShiftedLogKernelReal t (X * Real.exp (-t)) := by
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
        Real.log (X / (d : ℝ))) *
          (if t ≤ Real.log (X / (d : ℝ)) then (1 : ℝ) else 0)) =
      ∑ d ∈ S.filter (fun d : ℕ => t ≤ Real.log (X / (d : ℝ))),
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (X / (d : ℝ)) by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdt : t ≤ Real.log (X / (d : ℝ)) <;> simp [hdt]]
  rw [hfilter, moebiusShiftedLogKernelReal]
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

/-- A thresholded quadratic logarithmic Möbius sum is the shifted quadratic kernel. -/
theorem sum_moebius_log_sq_threshold_eq_shifted
    (X t : ℝ) (hX : 0 < X) (ht : 0 ≤ t) :
    (∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
      (((moebius d : ℤ) : ℝ) / (d : ℝ) *
        Real.log (X / (d : ℝ)) ^ (2 : ℕ)) *
          (if t ≤ Real.log (X / (d : ℝ)) then (1 : ℝ) else 0)) =
      moebiusShiftedLogSqKernelReal t (X * Real.exp (-t)) := by
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
        Real.log (X / (d : ℝ)) ^ (2 : ℕ)) *
          (if t ≤ Real.log (X / (d : ℝ)) then (1 : ℝ) else 0)) =
      ∑ d ∈ S.filter (fun d : ℕ => t ≤ Real.log (X / (d : ℝ))),
        ((moebius d : ℤ) : ℝ) / (d : ℝ) *
          Real.log (X / (d : ℝ)) ^ (2 : ℕ) by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdt : t ≤ Real.log (X / (d : ℝ)) <;> simp [hdt]]
  rw [hfilter, moebiusShiftedLogSqKernelReal]
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

end

end RHTower.Sieve
