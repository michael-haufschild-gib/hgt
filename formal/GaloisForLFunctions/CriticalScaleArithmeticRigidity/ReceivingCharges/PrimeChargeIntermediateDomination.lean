import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeIntermediateBounds
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeUniformScales

/-!
# Separating cutoff and horizon costs in the intermediate range

When `log N ≤ Q³²`, the overlap logarithm costs one cutoff logarithm.
When `Q⁸ ≤ N`, the remaining arithmetic boundary terms lose a positive
power of the horizon. These two facts separate every quadratic correction
into a vanishing cutoff mass and a bounded horizon factor.
-/

noncomputable section

open Finset MeasureTheory

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  CriticalArithmeticCorrelationTheory

private theorem half_rpow_sq (N : ℕ) : ((N : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = N := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

private theorem le_half_rpow_of_sq_le {N : ℕ} {x : ℝ} (hx : x ^ 2 ≤ N) :
    x ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
  have he := half_rpow_sq N
  have hp := Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 2 : ℝ)
  nlinarith only [hx, he, hp]

/-- The intermediate range charges at most one cutoff logarithm for overlap. -/
theorem primeCharge_intermediate_log_overlap {Q N : ℕ} {K : ℝ}
    (hK : 0 < K) (hL : 0 < Real.log N) (hsmall : Real.log N ≤ (Q : ℝ) ^ 32) :
    1 + Real.log (2 * K * Real.log N ^ (1 / 8 : ℝ)) ≤
      (5 + |Real.log (2 * K)|) * (1 + Real.log Q) := by
  have hlog := Real.log_le_log hL hsmall
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  rw [Real.log_mul (by positivity : (2 * K : ℝ) ≠ 0)
    (Real.rpow_pos_of_pos hL (1 / 8 : ℝ)).ne', Real.log_rpow hL]
  have hKlog := le_abs_self (Real.log (2 * K))
  have hq := Real.log_natCast_nonneg Q
  have hp := mul_nonneg (abs_nonneg (Real.log (2 * K))) hq
  nlinarith only [hlog, hKlog, hq, hp]

/-- The overlap square-root error is controlled by a single subcritical power. -/
theorem receiving_overlap_sqrt_cost_le {c L : ℝ} (hc : 1 ≤ c) (hL : 0 < L) :
    c ^ 2 * Real.sqrt ((1 + Real.log c) / L) ≤ Real.sqrt (c ^ 5 / L) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hlog := Real.log_le_sub_one_of_pos hc0
  have harg : 0 ≤ (1 + Real.log c) / L := by
    have := Real.log_nonneg hc
    positivity
  have hs : (c ^ 2 * Real.sqrt ((1 + Real.log c) / L)) ^ 2 ≤ c ^ 5 / L := by
    rw [mul_pow, Real.sq_sqrt harg]
    have h := mul_le_mul_of_nonneg_left
      (show 1 + Real.log c ≤ c by linarith only [hlog]) (pow_nonneg hc0.le 4)
    exact (div_le_div_of_nonneg_right h hL.le).trans_eq (by ring)
  have hr := Real.sq_sqrt (show 0 ≤ c ^ 5 / L by positivity)
  have hp := Real.sqrt_nonneg (c ^ 5 / L)
  nlinarith only [hs, hr, hp]

/-- The quartic conductor boundary costs half a horizon power. -/
theorem receiving_quartic_boundary_le {Q N : ℕ} {c : ℝ}
    (hN : 1 ≤ N) (hQ8 : Q ^ 8 ≤ N) (hc : 0 ≤ c) :
    c ^ 3 * (Q : ℝ) ^ 4 / N ≤ c ^ 3 / (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNR _
  have hq : (Q : ℝ) ^ 4 ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    le_half_rpow_of_sq_le (by
      rw [← pow_mul]
      norm_num only [show 4 * 2 = 8 by norm_num]
      exact_mod_cast hQ8)
  calc
    _ ≤ c ^ 3 * (N : ℝ) ^ (1 / 2 : ℝ) / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (pow_nonneg hc 3)) hNR.le
    _ = c ^ 3 * (N : ℝ) ^ (1 / 2 : ℝ) / ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [half_rpow_sq]
    _ = _ := by field_simp [hr.ne']

/-- The downward square-root error also loses half a horizon power after squaring. -/
theorem receiving_downward_sqrt_cost_le {Q N : ℕ} {c L : ℝ}
    (hN : 1 ≤ N) (hQ4 : Q ^ 4 ≤ N) (hc : 0 ≤ c) (hL : 0 ≤ L) :
    c ^ 2 * (Q : ℝ) * Real.sqrt (L / N) ≤
      Real.sqrt (c ^ 4 * L / (N : ℝ) ^ (1 / 2 : ℝ)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hNR _
  have hq : (Q : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    le_half_rpow_of_sq_le (by rw [← pow_mul]; exact_mod_cast hQ4)
  have hs : (c ^ 2 * (Q : ℝ) * Real.sqrt (L / N)) ^ 2 ≤
      c ^ 4 * L / (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL hNR.le)]
    calc
      _ = (c ^ 4 * L) * (Q : ℝ) ^ 2 / N := by ring
      _ ≤ (c ^ 4 * L) * (N : ℝ) ^ (1 / 2 : ℝ) / N :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hq (mul_nonneg (pow_nonneg hc 4) hL)) hNR.le
      _ = (c ^ 4 * L) * (N : ℝ) ^ (1 / 2 : ℝ) / ((N : ℝ) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [half_rpow_sq]
      _ = _ := by field_simp [hr.ne']
  have hroot := Real.sq_sqrt (show 0 ≤ c ^ 4 * L / (N : ℝ) ^ (1 / 2 : ℝ) by positivity)
  have hp := Real.sqrt_nonneg (c ^ 4 * L / (N : ℝ) ^ (1 / 2 : ℝ))
  nlinarith only [hs, hroot, hp]

/-- The polar near-Gram cost is bounded by the overlap-scaled polar square. -/
theorem receiving_polar_overlap_cost_le {c : ℝ} (hc : 1 ≤ c) (P : ℝ) :
    c * (1 + Real.log c) * P ^ 2 ≤ (c * P) ^ 2 := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hc)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show 1 + Real.log c ≤ c by linarith only [hlog]) hc0)
    (sq_nonneg P)).trans_eq (by ring)

#print axioms primeCharge_intermediate_log_overlap
#print axioms receiving_overlap_sqrt_cost_le
#print axioms receiving_quartic_boundary_le
#print axioms receiving_downward_sqrt_cost_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
