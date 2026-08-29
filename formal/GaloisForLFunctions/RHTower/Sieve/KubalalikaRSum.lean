import GaloisForLFunctions.RHTower.Sieve.KubalalikaDyadic
import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum

/-!
# The harmonic total of the block envelope

Dividing the five monomials by `r` and summing over `T^{1/4} ≤ r ≤ 2 T^{3/4}` turns them into the
sub-critical sums `Σ r^{-5/6}`, `Σ r^{-3/4}`, the tail `Σ r^{-3/2}` and two harmonic sums.  All
five totals sit at `T^{15/16}` up to one logarithm: this is the exact point of the parameter
choice `U ≍ T^{1/2}`, `V ≍ T^{1/8}`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem rpow_div_self {x : ℝ} (hx : 0 < x) (e : ℝ) : x ^ e / x = x ^ (e - 1) := by
  rw [Real.rpow_sub hx, Real.rpow_one]

/-- The five monomials of the scale envelope, divided by the shift. -/
theorem kubalalikaScalePower_div_eq {T : ℝ} {r : ℕ} (hr : 1 ≤ r) :
    kubalalikaScalePower T r / (r : ℝ)
      = T ^ (13 / 16 : ℝ) * (r : ℝ) ^ (-(5 / 6) : ℝ)
        + T * (r : ℝ) ^ (-(3 / 2) : ℝ)
        + T ^ (15 / 16 : ℝ) * (1 / (r : ℝ))
        + T ^ (3 / 4 : ℝ) * (r : ℝ) ^ (-(3 / 4) : ℝ)
        + T ^ (3 / 4 : ℝ) * (1 / (r : ℝ)) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h1 : (r : ℝ) ^ (1 / 6 : ℝ) / (r : ℝ) = (r : ℝ) ^ (-(5 / 6) : ℝ) := by
    rw [rpow_div_self hr0]
    norm_num
  have h2 : (r : ℝ) ^ (-(1 / 2) : ℝ) / (r : ℝ) = (r : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [rpow_div_self hr0]
    norm_num
  have h3 : (r : ℝ) ^ (1 / 4 : ℝ) / (r : ℝ) = (r : ℝ) ^ (-(3 / 4) : ℝ) := by
    rw [rpow_div_self hr0]
    norm_num
  rw [kubalalikaScalePower, add_div, add_div, add_div, add_div]
  have d1 : T ^ (13 / 16 : ℝ) * (r : ℝ) ^ (1 / 6 : ℝ) / (r : ℝ)
      = T ^ (13 / 16 : ℝ) * (r : ℝ) ^ (-(5 / 6) : ℝ) := by rw [mul_div_assoc, h1]
  have d2 : T * (r : ℝ) ^ (-(1 / 2) : ℝ) / (r : ℝ) = T * (r : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [mul_div_assoc, h2]
  have d3 : T ^ (15 / 16 : ℝ) / (r : ℝ) = T ^ (15 / 16 : ℝ) * (1 / (r : ℝ)) := by
    rw [mul_one_div]
  have d4 : T ^ (3 / 4 : ℝ) * (r : ℝ) ^ (1 / 4 : ℝ) / (r : ℝ)
      = T ^ (3 / 4 : ℝ) * (r : ℝ) ^ (-(3 / 4) : ℝ) := by rw [mul_div_assoc, h3]
  have d5 : T ^ (3 / 4 : ℝ) / (r : ℝ) = T ^ (3 / 4 : ℝ) * (1 / (r : ℝ)) := by rw [mul_one_div]
  rw [d1, d2, d3, d4, d5]

/-- **The harmonic total of the block envelope.** -/
theorem sum_kubalalikaScalePower_div_le {T : ℝ} (hT : 1 ≤ T) {rLo rHi : ℕ}
    (hrLo : 1 ≤ rLo) (hlo : T ^ (1 / 4 : ℝ) ≤ (rLo : ℝ))
    (hhi : (rHi : ℝ) ≤ 2 * T ^ (3 / 4 : ℝ)) :
    ∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ)
      ≤ 30 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hlogT : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT
  have hT15 : (0 : ℝ) < T ^ (15 / 16 : ℝ) := Real.rpow_pos_of_pos hT0 _
  rcases lt_or_ge rHi rLo with hempty | hne
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  have hrHi : 1 ≤ rHi := le_trans hrLo hne
  have hrHi0 : (0 : ℝ) < (rHi : ℝ) := by exact_mod_cast hrHi
  have hrHi1 : (1 : ℝ) ≤ (rHi : ℝ) := by exact_mod_cast hrHi
  have hrLo0 : (0 : ℝ) < (rLo : ℝ) := by exact_mod_cast hrLo
  -- rewrite the summand
  have hcongr : ∑ r ∈ Finset.Icc rLo rHi, kubalalikaScalePower T r / (r : ℝ)
      = ∑ r ∈ Finset.Icc rLo rHi,
          (T ^ (13 / 16 : ℝ) * (r : ℝ) ^ (-(5 / 6) : ℝ)
            + T * (r : ℝ) ^ (-(3 / 2) : ℝ)
            + T ^ (15 / 16 : ℝ) * (1 / (r : ℝ))
            + T ^ (3 / 4 : ℝ) * (r : ℝ) ^ (-(3 / 4) : ℝ)
            + T ^ (3 / 4 : ℝ) * (1 / (r : ℝ))) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    exact kubalalikaScalePower_div_eq (le_trans hrLo (Finset.mem_Icc.mp hr).1)
  rw [hcongr]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  -- the four kernels
  have hsub : Finset.Icc rLo rHi ⊆ Finset.Icc 1 rHi := by
    intro r hr
    rw [Finset.mem_Icc] at hr ⊢
    exact ⟨le_trans hrLo hr.1, hr.2⟩
  have hS1 : ∑ r ∈ Finset.Icc rLo rHi, (r : ℝ) ^ (-(5 / 6) : ℝ)
      ≤ (rHi : ℝ) ^ (1 / 6 : ℝ) * 6 + 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun r : ℕ => (r : ℝ) ^ (-(5 / 6) : ℝ)) hsub
      (fun r _ _ => Real.rpow_nonneg (Nat.cast_nonneg r) _)
    refine le_trans h ?_
    have hk := sum_rpow_neg_subcritical_le (c := 5 / 6) (by norm_num) (by norm_num) rHi
    have hval : (rHi : ℝ) ^ (1 - 5 / 6 : ℝ) / (1 - 5 / 6 : ℝ) + 1
        = (rHi : ℝ) ^ (1 / 6 : ℝ) * 6 + 1 := by
      norm_num
      ring
    linarith [hval ▸ hk]
  have hS4 : ∑ r ∈ Finset.Icc rLo rHi, (r : ℝ) ^ (-(3 / 4) : ℝ)
      ≤ (rHi : ℝ) ^ (1 / 4 : ℝ) * 4 + 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun r : ℕ => (r : ℝ) ^ (-(3 / 4) : ℝ)) hsub
      (fun r _ _ => Real.rpow_nonneg (Nat.cast_nonneg r) _)
    refine le_trans h ?_
    have hk := sum_rpow_neg_subcritical_le (c := 3 / 4) (by norm_num) (by norm_num) rHi
    have hval : (rHi : ℝ) ^ (1 - 3 / 4 : ℝ) / (1 - 3 / 4 : ℝ) + 1
        = (rHi : ℝ) ^ (1 / 4 : ℝ) * 4 + 1 := by
      norm_num
      ring
    linarith [hval ▸ hk]
  have hS2 : ∑ r ∈ Finset.Icc rLo rHi, (r : ℝ) ^ (-(3 / 2) : ℝ)
      ≤ 3 * (rLo : ℝ) ^ (-(1 / 2) : ℝ) := by
    have hk := sum_rpow_neg_tail_le (c := 3 / 2) (by norm_num) (R := rLo) (N := rHi) hrLo
    have hval : ((3 / 2 : ℝ) / (3 / 2 - 1)) * (rLo : ℝ) ^ (1 - 3 / 2 : ℝ)
        = 3 * (rLo : ℝ) ^ (-(1 / 2) : ℝ) := by
      norm_num
    linarith [hval ▸ hk]
  have hS3 : ∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)) ≤ 1 + Real.log rHi := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun r : ℕ => (1 : ℝ) / (r : ℝ)) hsub
      (fun r _ _ => by positivity)
    refine le_trans h ?_
    have := invSum_le_one_add_log hrHi
    rw [invSum] at this
    exact this
  -- substitute the ranges
  have hhi6 : (rHi : ℝ) ^ (1 / 6 : ℝ) ≤ 2 * T ^ (1 / 8 : ℝ) := by
    calc (rHi : ℝ) ^ (1 / 6 : ℝ) ≤ (2 * T ^ (3 / 4 : ℝ)) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow hrHi0.le hhi (by norm_num)
      _ = (2 : ℝ) ^ (1 / 6 : ℝ) * T ^ (1 / 8 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _),
            ← Real.rpow_mul hT0.le]
          norm_num
      _ ≤ 2 * T ^ (1 / 8 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hT0.le _)
          calc (2 : ℝ) ^ (1 / 6 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hhi4 : (rHi : ℝ) ^ (1 / 4 : ℝ) ≤ 2 * T ^ (3 / 16 : ℝ) := by
    calc (rHi : ℝ) ^ (1 / 4 : ℝ) ≤ (2 * T ^ (3 / 4 : ℝ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hrHi0.le hhi (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) * T ^ (3 / 16 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _),
            ← Real.rpow_mul hT0.le]
          norm_num
      _ ≤ 2 * T ^ (3 / 16 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hT0.le _)
          calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  have hlo2 : (rLo : ℝ) ^ (-(1 / 2) : ℝ) ≤ T ^ (-(1 / 8) : ℝ) := by
    have h := rpow_neg_le_rpow_neg (x := T ^ (1 / 4 : ℝ)) (y := (rLo : ℝ))
      (Real.rpow_pos_of_pos hT0 _) hlo (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hval : (T ^ (1 / 4 : ℝ)) ^ (-(1 / 2) : ℝ) = T ^ (-(1 / 8) : ℝ) := by
      rw [← Real.rpow_mul hT0.le]
      norm_num
    rwa [hval] at h
  have hlogHi : Real.log rHi ≤ 1 + Real.log T := by
    have h1 : Real.log rHi ≤ Real.log (2 * T ^ (3 / 4 : ℝ)) := Real.log_le_log hrHi0 hhi
    have h2 : Real.log (2 * T ^ (3 / 4 : ℝ)) = Real.log 2 + (3 / 4) * Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hT0]
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  -- the five totals
  have hpow : ∀ e : ℝ, e ≤ 15 / 16 → T ^ e ≤ T ^ (15 / 16 : ℝ) := fun e he =>
    Real.rpow_le_rpow_of_exponent_le hT he
  have hcomb1 : T ^ (13 / 16 : ℝ) * T ^ (1 / 8 : ℝ) = T ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have hcomb4 : T ^ (3 / 4 : ℝ) * T ^ (3 / 16 : ℝ) = T ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_add hT0]
    norm_num
  have hcomb2 : T * T ^ (-(1 / 8) : ℝ) = T ^ (7 / 8 : ℝ) := by
    nth_rewrite 1 [show T = T ^ (1 : ℝ) from (Real.rpow_one T).symm]
    rw [← Real.rpow_add hT0]
    norm_num
  have hT13 : T ^ (13 / 16 : ℝ) ≤ T ^ (15 / 16 : ℝ) := hpow _ (by norm_num)
  have hT34 : T ^ (3 / 4 : ℝ) ≤ T ^ (15 / 16 : ℝ) := hpow _ (by norm_num)
  have hT78 : T ^ (7 / 8 : ℝ) ≤ T ^ (15 / 16 : ℝ) := hpow _ (by norm_num)
  have hT130 : (0 : ℝ) < T ^ (13 / 16 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hT340 : (0 : ℝ) < T ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hterm1 : T ^ (13 / 16 : ℝ) * ((rHi : ℝ) ^ (1 / 6 : ℝ) * 6 + 1)
      ≤ 13 * T ^ (15 / 16 : ℝ) := by
    have h1 : (rHi : ℝ) ^ (1 / 6 : ℝ) * 6 + 1 ≤ 12 * T ^ (1 / 8 : ℝ) + 1 := by linarith
    have h2 : T ^ (13 / 16 : ℝ) * (12 * T ^ (1 / 8 : ℝ) + 1)
        = 12 * T ^ (15 / 16 : ℝ) + T ^ (13 / 16 : ℝ) := by
      rw [← hcomb1]; ring
    calc T ^ (13 / 16 : ℝ) * ((rHi : ℝ) ^ (1 / 6 : ℝ) * 6 + 1)
        ≤ T ^ (13 / 16 : ℝ) * (12 * T ^ (1 / 8 : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 hT130.le
      _ = 12 * T ^ (15 / 16 : ℝ) + T ^ (13 / 16 : ℝ) := h2
      _ ≤ 13 * T ^ (15 / 16 : ℝ) := by linarith
  have hterm4 : T ^ (3 / 4 : ℝ) * ((rHi : ℝ) ^ (1 / 4 : ℝ) * 4 + 1)
      ≤ 9 * T ^ (15 / 16 : ℝ) := by
    have h1 : (rHi : ℝ) ^ (1 / 4 : ℝ) * 4 + 1 ≤ 8 * T ^ (3 / 16 : ℝ) + 1 := by linarith
    have h2 : T ^ (3 / 4 : ℝ) * (8 * T ^ (3 / 16 : ℝ) + 1)
        = 8 * T ^ (15 / 16 : ℝ) + T ^ (3 / 4 : ℝ) := by
      rw [← hcomb4]; ring
    calc T ^ (3 / 4 : ℝ) * ((rHi : ℝ) ^ (1 / 4 : ℝ) * 4 + 1)
        ≤ T ^ (3 / 4 : ℝ) * (8 * T ^ (3 / 16 : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 hT340.le
      _ = 8 * T ^ (15 / 16 : ℝ) + T ^ (3 / 4 : ℝ) := h2
      _ ≤ 9 * T ^ (15 / 16 : ℝ) := by linarith
  have hterm2 : T * (3 * (rLo : ℝ) ^ (-(1 / 2) : ℝ)) ≤ 3 * T ^ (15 / 16 : ℝ) := by
    have h1 : 3 * (rLo : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 * T ^ (-(1 / 8) : ℝ) := by linarith
    calc T * (3 * (rLo : ℝ) ^ (-(1 / 2) : ℝ)) ≤ T * (3 * T ^ (-(1 / 8) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 hT0.le
      _ = 3 * T ^ (7 / 8 : ℝ) := by rw [← hcomb2]; ring
      _ ≤ 3 * T ^ (15 / 16 : ℝ) := by linarith
  have hterm3 : T ^ (15 / 16 : ℝ) * (1 + Real.log rHi)
      ≤ 2 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) := by
    have h1 : 1 + Real.log rHi ≤ 2 * (1 + Real.log T) := by linarith
    calc T ^ (15 / 16 : ℝ) * (1 + Real.log rHi)
        ≤ T ^ (15 / 16 : ℝ) * (2 * (1 + Real.log T)) :=
          mul_le_mul_of_nonneg_left h1 hT15.le
      _ = 2 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) := by ring
  have hterm5 : T ^ (3 / 4 : ℝ) * (1 + Real.log rHi)
      ≤ 2 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) := by
    have h1 : 1 + Real.log rHi ≤ 2 * (1 + Real.log T) := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Real.log rHi := by
      have := Real.log_nonneg hrHi1
      linarith
    calc T ^ (3 / 4 : ℝ) * (1 + Real.log rHi)
        ≤ T ^ (15 / 16 : ℝ) * (1 + Real.log rHi) :=
          mul_le_mul_of_nonneg_right hT34 h2
      _ ≤ T ^ (15 / 16 : ℝ) * (2 * (1 + Real.log T)) :=
          mul_le_mul_of_nonneg_left h1 hT15.le
      _ = 2 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) := by ring
  -- assemble
  have hm1 : T ^ (13 / 16 : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (r : ℝ) ^ (-(5 / 6) : ℝ))
      ≤ 13 * T ^ (15 / 16 : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hS1 hT130.le) hterm1
  have hm2 : T * (∑ r ∈ Finset.Icc rLo rHi, (r : ℝ) ^ (-(3 / 2) : ℝ))
      ≤ 3 * T ^ (15 / 16 : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hS2 hT0.le) hterm2
  have hm3 : T ^ (15 / 16 : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)))
      ≤ 2 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) :=
    le_trans (mul_le_mul_of_nonneg_left hS3 hT15.le) hterm3
  have hm4 : T ^ (3 / 4 : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (r : ℝ) ^ (-(3 / 4) : ℝ))
      ≤ 9 * T ^ (15 / 16 : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left hS4 hT340.le) hterm4
  have hm5 : T ^ (3 / 4 : ℝ) * (∑ r ∈ Finset.Icc rLo rHi, (1 / (r : ℝ)))
      ≤ 2 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) :=
    le_trans (mul_le_mul_of_nonneg_left hS3 hT340.le) hterm5
  have hfinal : (13 : ℝ) * T ^ (15 / 16 : ℝ) + 3 * T ^ (15 / 16 : ℝ) + 9 * T ^ (15 / 16 : ℝ)
      ≤ 25 * T ^ (15 / 16 : ℝ) * (1 + Real.log T) := by
    nlinarith only [hT15, hlogT]
  linarith

end

end RHTower.Sieve
