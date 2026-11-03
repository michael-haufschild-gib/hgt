import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheEighthRootComplementKeepsItsBlockReserves

/-!
# The first two bands retain coercivity at critical overlap

The conductor cutoff `Q = floor(L^(13/32))` pays the mid-band error
`c sqrt(c) (1 + log c) / sqrt(Q)` even at `c = L^(1/8)`.
The remaining losses decay by powers of `L`; the first band retains a fixed
positive floor and the second retains a multiple of `sqrt(L)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- Critical overlap still pays both band errors and leaves positive block floors.
The gap `13/64 - 3/16 = 1/64` absorbs the logarithmic mid-band loss. -/
theorem critical_first_band_scalar_smallness
    {N Q₁ R₀ : ℕ} {c L Lh κ₀ C_small0 C_coerc0 C_band1 C_cross01 : ℝ}
    (hc1 : 1 ≤ c) (hcup : c ≤ L ^ (1 / 8 : ℝ)) (hL1 : 1 ≤ L) (hLh_eq : Lh = L ^ (1 / 2 : ℝ))
    (hκ₀ : 0 < κ₀)
    (hC_small0 : 0 < C_small0) (hC_cross01 : 0 < C_cross01)
    (hVc : 1 + Real.log c ≤ L ^ (1 / 128 : ℝ))
    (hsqrtQ : (1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2) ≤ Real.sqrt Q₁)
    (hlogQ_lb : (13 / 32 : ℝ) * Real.log L - 1 ≤ Real.log (Q₁ : ℝ))
    (hH₀_ub : 1 + Real.log (R₀ : ℝ) ≤ 2 * Lh)
    (hlogR₀_lb : Lh - 1 ≤ Real.log (R₀ : ℝ))
    (hR₀_tail : (R₀ : ℝ) * Real.sqrt (L / N) ≤ 1 / L)
    (hc5N : c ^ 5 * L / N ≤ 1 / L)
    (hc3R₀4 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ 1 / L)
    (hc3R₀2 : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / N) ≤ 1 / L)
    (hν_b1 : C_small0 * 18 ≤ L ^ (1 / 128 : ℝ))
    (hν_b2 : C_cross01 * 4 ≤ L ^ (1 / 128 : ℝ))
    (hν_b6 : 32 * C_band1 ≤ L ^ (1 / 128 : ℝ))
    (hll_scaled : κ₀ + 4 + C_coerc0 + 3 / 4 ≤ ((3 / 4 : ℝ) * (13 / 32 : ℝ) - (1 / 8 : ℝ)) * Real.log L)
    (hL_Lh_gap : (8 * (κ₀ + 3)) ^ 2 ≤ L) :
    C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 ∧
    C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 ∧
    κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 ∧
    κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := by rw [hLh_eq]; exact Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    rw [hLh_eq, ← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hlc_ge1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
  have hlc_nn : 0 ≤ 1 + Real.log c := zero_le_one.trans hlc_ge1
  have hLν0 : 0 ≤ L ^ (1 / 128 : ℝ) := Real.rpow_nonneg hL0.le _
  have hLmν0 : 0 ≤ L ^ (-(1 / 128 : ℝ)) := Real.rpow_nonneg hL0.le _
  have hmul_ν : L ^ (1 / 128 : ℝ) * L ^ (-(1 / 128 : ℝ)) = 1 := by
    rw [← Real.rpow_add hL0, show (1 / 128 : ℝ) + (-(1 / 128 : ℝ)) = 0 by ring, Real.rpow_zero]
  have h1_invL : 1 / L ≤ L ^ (-(1 / 128 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h1_invLh : 1 / Lh ≤ L ^ (-(1 / 128 : ℝ)) := by
    rw [hLh_eq, one_div, ← Real.rpow_neg hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hH₀_div : (1 + Real.log (R₀ : ℝ)) / L ≤ 2 / Lh := by
    rw [div_le_div_iff₀ hL0 hLh0]
    calc
      (1 + Real.log (R₀ : ℝ)) * Lh ≤ (2 * Lh) * Lh := mul_le_mul_of_nonneg_right hH₀_ub hLh0.le
      _ = 2 * (Lh * Lh) := by ring
      _ = 2 * L := by rw [hLh_sq]
  have hc2_vc_Lh : c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (-(1 / 128 : ℝ)) := by
    have h1 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 2 1 (2 * (1 / 8 : ℝ) + (1 / 128 : ℝ)) (by push_cast; linarith)
    rw [pow_one] at h1
    calc c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (2 * (1 / 8 : ℝ) + (1 / 128 : ℝ)) / L ^ (1 / 2 : ℝ) := by
          rw [← hLh_eq]; exact div_le_div_of_nonneg_right h1 hLh0.le
      _ ≤ L ^ (-(1 / 128 : ℝ)) := rpow_div_rpow_le hL1 (by linarith)
  have hc2_vc_L : c ^ 2 * (1 + Real.log c) / L ≤ L ^ (-(1 / 128 : ℝ)) :=
    (div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg c) hlc_nn) hLh0
      (by nlinarith only [hLh1, hLh_sq])).trans hc2_vc_Lh
  have hc4_vc : c ^ 4 * (1 + Real.log c) / L ≤ L ^ (-(1 / 128 : ℝ)) := by
    have h1 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 4 1 (4 * (1 / 8 : ℝ) + (1 / 128 : ℝ)) (by push_cast; linarith)
    rw [pow_one] at h1
    calc c ^ 4 * (1 + Real.log c) / L ≤ L ^ (4 * (1 / 8 : ℝ) + (1 / 128 : ℝ)) / L ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ L ^ (-(1 / 128 : ℝ)) := rpow_div_rpow_le hL1 (by linarith)
  have hc7_L : c ^ 7 / L ≤ L ^ (-(1 / 128 : ℝ)) := by
    have h1 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 7 0 (7 * (1 / 8 : ℝ)) (by push_cast; linarith)
    rw [pow_zero, mul_one] at h1
    calc c ^ 7 / L ≤ L ^ (7 * (1 / 8 : ℝ)) / L ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact div_le_div_of_nonneg_right h1 hL0.le
      _ ≤ L ^ (-(1 / 128 : ℝ)) := rpow_div_rpow_le hL1 (by linarith)
  -- 1. Band 0 smallness
  have hout1 : C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hmid_Q₁ : c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤ 2 * L ^ (-(1 / 128 : ℝ)) := by
      have hc32 : c * Real.sqrt c ≤ L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ)) := by
        have hsq : (c * Real.sqrt c) ^ 2 ≤ (L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc0.le, show c ^ 2 * c = c ^ 3 by ring,
            ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le]
          have h3 := monomial_le_rpow hL1 hc0.le hcup hlc_nn hVc 3 0 (3 * (1 / 8 : ℝ)) (by push_cast; linarith)
          rw [pow_zero, mul_one] at h3
          exact h3.trans_eq (by congr 1; push_cast; ring)
        have hp1 : 0 ≤ c * Real.sqrt c := mul_nonneg hc0.le (Real.sqrt_nonneg c)
        have hp2 : 0 ≤ L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ)) := Real.rpow_nonneg hL0.le _
        nlinarith only [hsq, hp1, hp2]
      have hden_pos : 0 < (1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2) :=
        mul_pos (by norm_num) (Real.rpow_pos_of_pos hL0 _)
      calc
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤
            (L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ)) * L ^ (1 / 128 : ℝ)) / ((1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2)) :=
          (div_le_div_of_nonneg_right
            (mul_le_mul hc32 hVc hlc_nn (Real.rpow_nonneg hL0.le _))
            (Real.sqrt_nonneg _)).trans
            (div_le_div_of_nonneg_left
              (mul_nonneg (Real.rpow_nonneg hL0.le _) hLν0) hden_pos hsqrtQ)
        _ = 2 * L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ) + (1 / 128 : ℝ) - (13 / 32 : ℝ) / 2) := by
          rw [show (L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ)) * L ^ (1 / 128 : ℝ)) / ((1 / 2 : ℝ) * L ^ ((13 / 32 : ℝ) / 2)) =
            2 * ((L ^ ((3 / 2 : ℝ) * (1 / 8 : ℝ)) * L ^ (1 / 128 : ℝ)) / L ^ ((13 / 32 : ℝ) / 2)) by ring,
            ← Real.rpow_add hL0, ← Real.rpow_sub hL0]
        _ ≤ 2 * L ^ (-(1 / 128 : ℝ)) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) zero_le_two
    have ht4 : c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L ≤ 2 * L ^ (-(1 / 128 : ℝ)) := by
      calc
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L =
            c ^ 2 * (1 + Real.log c) * ((1 + Real.log R₀) / L) := by ring
        _ ≤ c ^ 2 * (1 + Real.log c) * (2 / Lh) :=
          mul_le_mul_of_nonneg_left hH₀_div (mul_nonneg (sq_nonneg c) hlc_nn)
        _ = 2 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
        _ ≤ 2 * L ^ (-(1 / 128 : ℝ)) := mul_le_mul_of_nonneg_left hc2_vc_Lh zero_le_two
    have hlogR₀_nn : 0 ≤ 1 + Real.log (R₀ : ℝ) := by linarith [Real.log_natCast_nonneg R₀]
    have ht1 : c * (1 + Real.log c) * (1 + Real.log R₀) / L ≤ 2 * L ^ (-(1 / 128 : ℝ)) := by
      have hm : c * (1 + Real.log c) ≤ c ^ 2 * (1 + Real.log c) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hc1]) hlc_nn
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm hlogR₀_nn) hL0.le).trans
        ((by ring : c ^ 2 * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L).trans_le ht4)
    have ht2 : c * (1 + Real.log R₀) / L ≤ 2 * L ^ (-(1 / 128 : ℝ)) :=
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hc0.le hlc_ge1) hlogR₀_nn) hL0.le).trans ht1
    have ht3 : c ^ 2 / L ≤ L ^ (-(1 / 128 : ℝ)) :=
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) hlc_ge1) hL0.le).trans
        hc2_vc_L
    have ht5 : c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) ≤ L ^ (-(1 / 128 : ℝ)) := by
      calc
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) = c ^ 2 * ((R₀ : ℝ) * Real.sqrt (L / N)) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR₀_tail (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ L ^ (-(1 / 128 : ℝ)) := ht3
    have ht6 : c ^ 5 * L / N ≤ L ^ (-(1 / 128 : ℝ)) := hc5N.trans h1_invL
    have ht8 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ L ^ (-(1 / 128 : ℝ)) := hc3R₀4.trans h1_invL
    have hsum18 : c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤ 18 * L ^ (-(1 / 128 : ℝ)) := by
      linarith only [ht1, ht2, ht3, ht4, ht5, ht6, hmid_Q₁, ht8, hc2_vc_L, hLmν0]
    calc
      _ ≤ C_small0 * (18 * L ^ (-(1 / 128 : ℝ))) := mul_le_mul_of_nonneg_left hsum18 hC_small0.le
      _ = (C_small0 * 18) * L ^ (-(1 / 128 : ℝ)) := by ring
      _ ≤ L ^ (1 / 128 : ℝ) * L ^ (-(1 / 128 : ℝ)) := mul_le_mul_of_nonneg_right hν_b1 hLmν0
      _ = 1 := hmul_ν
  -- 2. Cross (u₀, u₁) smallness
  have hout2 : C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 := by
    have hc3_N : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ L ^ (-(1 / 128 : ℝ)) := hc3R₀2.trans h1_invL
    have hsum4 : 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 4 * L ^ (-(1 / 128 : ℝ)) := by
      linarith only [h1_invLh, hc2_vc_Lh, hc4_vc, hc3_N]
    calc
      _ ≤ C_cross01 * (4 * L ^ (-(1 / 128 : ℝ))) := mul_le_mul_of_nonneg_left hsum4 hC_cross01.le
      _ = (C_cross01 * 4) * L ^ (-(1 / 128 : ℝ)) := by ring
      _ ≤ L ^ (1 / 128 : ℝ) * L ^ (-(1 / 128 : ℝ)) := mul_le_mul_of_nonneg_right hν_b2 hLmν0
      _ = 1 := hmul_ν
  -- 3. Band 0 floor
  have hout3 : κ₀ + 3 + 1 / 2 ≤ (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) - Real.log c - C_coerc0 := by
    have hlogc : Real.log c ≤ (1 / 8 : ℝ) * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 (1 / 8 : ℝ))
    have hq_scaled : (3 / 4 : ℝ) * (13 / 32 : ℝ) * Real.log L - 3 / 4 ≤
        (3 / 4 : ℝ) * Real.log (Q₁ : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb (by norm_num : (0 : ℝ) ≤ 3 / 4)
      linarith only [hm]
    linarith only [hlogc, hq_scaled, hll_scaled]
  -- 4. Band 1 floor with the reserve `√L/32`
  have hout4 : κ₀ + 2 + Lh / 32 + (1 / 16 : ℝ) * Lh + 1 / 4 ≤
      (1 / 4 : ℝ) * Real.log (R₀ : ℝ) - C_band1 * c ^ 2 * (1 + Real.log c) := by
    have hc2_Lh : C_band1 * c ^ 2 * (1 + Real.log c) ≤ Lh / 32 := by
      have h1 : (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ 1 := by
        calc
          (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ L ^ (1 / 128 : ℝ) * L ^ (-(1 / 128 : ℝ)) :=
            mul_le_mul hν_b6 hc2_vc_Lh
              (div_nonneg (mul_nonneg (sq_nonneg c) hlc_nn) hLh0.le) hLν0
          _ = 1 := hmul_ν
      have hm := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ Lh / 32)
      have hid : (32 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) * (Lh / 32) =
          C_band1 * c ^ 2 * (1 + Real.log c) := by field_simp
      linarith only [hm, hid]
    have hLh_lb : 8 * (κ₀ + 3) ≤ Lh := by
      have hsq : (8 * (κ₀ + 3)) ^ 2 ≤ Lh ^ 2 := by rw [sq Lh, hLh_sq]; exact hL_Lh_gap
      have hp : 0 ≤ 8 * (κ₀ + 3) := by linarith only [hκ₀]
      nlinarith only [hsq, hp, hLh0]
    linarith only [hlogR₀_lb, hc2_Lh, hLh_lb, hκ₀]
  exact ⟨hout1, hout2, hout3, hout4⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
