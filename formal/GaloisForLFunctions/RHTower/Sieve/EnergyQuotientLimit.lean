import GaloisForLFunctions.RHTower.Sieve.BudgetScaleLimits
import GaloisForLFunctions.RHTower.Sieve.OmegaEnergyBound
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The coefficient energy, normalised

The weighted coefficient energy over the fibre is negligible against the product of the fibre range,
the window length and the squared harmonic mass.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The fibre range dominates the square root of the outer scale. -/
theorem sqrt_le_budgetB {β : ℝ} (x : ℝ) (h1 : (1 : ℝ) ≤ cardLength β x) :
    Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := by
  rw [budgetB]
  have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
  linarith

/-- The reciprocal fibre range vanishes. -/
theorem tendsto_inv_budgetB {β : ℝ} (hβ0 : 0 < β) :
    Tendsto (fun x : ℝ => 1 / ((budgetB β x : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ => 1 / Real.sqrt x) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop Real.tendsto_sqrt_atTop 1
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hx hh1
    have := sqrt_le_budgetB (β := β) x hh1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
    have : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
    positivity
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ)] with x hx hh1
    have hB := sqrt_le_budgetB (β := β) x hh1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
    exact div_le_div_of_nonneg_left zero_le_one hsx hB

/-- The harmonic sum over the ladder is negligible against the window length. -/
theorem tendsto_mertensS_div_cardLength {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    Tendsto (fun x : ℝ => mertensS (ladderTop β γ x) / cardLength β x) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ =>
      (β + |mertensSecondUpperConst|)
        * ((Real.log x) ^ (1 : ℝ) * Real.exp (-((Real.log x) ^ β)))) atTop (𝓝 0) := by
    have := tendsto_rpow_log_mul_exp_neg (c := (1 : ℝ)) (a := β) hβ0
    simpa using this.const_mul (β + |mertensSecondUpperConst|)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ] with x hfacts
    have := mertensS_nonneg' (ladderTop β γ x)
    have := cardLength_pos β x
    positivity
  · filter_upwards [eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
      Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)]
      with x hfacts hx1 hlogx1
    obtain ⟨hz2, hzh, -⟩ := hfacts
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hlogh : Real.log (cardLength β x) = (Real.log x) ^ β := log_cardLength β x
    have hz2R : (2 : ℝ) ≤ ((ladderTop β γ x : ℕ) : ℝ) := by exact_mod_cast hz2
    have hlogz : Real.log 2 ≤ Real.log ((ladderTop β γ x : ℕ) : ℝ) :=
      Real.log_le_log (by norm_num) hz2R
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hmono : Real.log (Real.log ((ladderTop β γ x : ℕ) : ℝ))
        ≤ Real.log ((Real.log x) ^ β) := by
      rw [← hlogh]
      refine Real.log_le_log (by linarith) ?_
      exact Real.log_le_log (by linarith) hzh
    have hval : Real.log ((Real.log x) ^ β) = β * Real.log (Real.log x) :=
      Real.log_rpow hlogx β
    have hmert : mertensS (ladderTop β γ x)
        ≤ β * Real.log (Real.log x) + mertensSecondUpperConst := by
      have := mertensS_le (N := ladderTop β γ x) hz2
      rw [logLog] at this
      linarith [hmono, hval]
    have hll : Real.log (Real.log x) ≤ Real.log x := by
      have := Real.log_le_sub_one_of_pos hlogx
      linarith
    have hC : mertensSecondUpperConst ≤ |mertensSecondUpperConst| := le_abs_self _
    have hnum : mertensS (ladderTop β γ x)
        ≤ (β + |mertensSecondUpperConst|) * Real.log x := by
      have h1 : β * Real.log (Real.log x) ≤ β * Real.log x :=
        mul_le_mul_of_nonneg_left hll hβ0.le
      nlinarith [hmert, h1, hC, hlogx1, abs_nonneg mertensSecondUpperConst]
    have hhinv : 1 / cardLength β x = Real.exp (-((Real.log x) ^ β)) := by
      rw [cardLength, one_div, ← Real.exp_neg]
    have hnn : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg' _
    calc mertensS (ladderTop β γ x) / cardLength β x
        = mertensS (ladderTop β γ x) * (1 / cardLength β x) := by ring
      _ ≤ ((β + |mertensSecondUpperConst|) * Real.log x) * (1 / cardLength β x) := by
          refine mul_le_mul_of_nonneg_right hnum ?_
          positivity
      _ = (β + |mertensSecondUpperConst|)
            * ((Real.log x) ^ (1 : ℝ) * Real.exp (-((Real.log x) ^ β))) := by
          rw [hhinv, Real.rpow_one]
          ring

/-- **The normalised coefficient energy vanishes.** -/
theorem tendsto_energy_quotient {β γ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hγβ : γ * β < 1) :
    Tendsto (fun x : ℝ =>
        (∑ n ∈ Finset.Icc 1 (budgetB β x),
            ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
          / (((budgetB β x : ℕ) : ℝ) * cardLength β x
            * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2))
      atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ =>
      8 * (mertensS (ladderTop β γ x) / cardLength β x)
        + 16 * (1 / ((budgetB β x : ℕ) : ℝ))
        + 64 * (cardLength β x / ((budgetB β x : ℕ) : ℝ))
        + 2 * (1 / cardLength β x)) atTop (𝓝 0) := by
    have h1 := (tendsto_mertensS_div_cardLength hβ0 hβ1 hγ0 hγ1 hγβ).const_mul (8 : ℝ)
    have h2 := (tendsto_inv_budgetB (β := β) hβ0).const_mul (16 : ℝ)
    have h3 := (tendsto_cardLength_div_budgetB hβ0 hβ1).const_mul (64 : ℝ)
    have h4 := (tendsto_inv_cardLength (β := β) hβ0).const_mul (2 : ℝ)
    simpa using ((h1.add h2).add h3).add h4
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
      (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ),
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hfacts hW hh1 hx1
    have hsum : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 (budgetB β x),
        ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    have hB : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
    have hh0 : (0 : ℝ) < cardLength β x := by linarith
    have hden : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) * cardLength β x
        * (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
      have : (0 : ℝ) < (mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x)) ^ 2 := by
        nlinarith [hW]
      exact mul_pos (mul_pos hB0 hh0) this
    exact div_nonneg hsum hden.le
  · filter_upwards [eventually_ladderTop_facts hβ0 hγ0 hγ1 hγβ,
      (tendsto_ladderMass hβ0 hγ0 hγ1 hγβ).eventually_ge_atTop (1 : ℝ),
      (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (1 : ℝ)] with x hfacts hW hh1 hx1
    obtain ⟨hz2, hzh, hz₀z⟩ := hfacts
    set W : ℝ := mertensS (ladderTop β γ x) - mertensS (siftStart (γ * β) x) with hWdef
    have hB : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := sqrt_le_budgetB (β := β) x hh1
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    have hB0 : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) := by linarith
    have hh0 : (0 : ℝ) < cardLength β x := by linarith
    have hW2 : (1 : ℝ) ≤ W ^ 2 := by nlinarith [hW]
    have hW20 : (0 : ℝ) < W ^ 2 := by linarith
    have hden : (0 : ℝ) < ((budgetB β x : ℕ) : ℝ) * cardLength β x * W ^ 2 :=
      mul_pos (mul_pos hB0 hh0) hW20
    have hE := sum_normSq_omegaCoeff_Icc_le (z₀ := siftStart (γ * β) x)
      (z := ladderTop β γ x) hz₀z (A := 1) (B := budgetB β x) le_rfl
    have hpi := card_primesLE_le (ladderTop β γ x)
    have hzR : ((ladderTop β γ x : ℕ) : ℝ) ≤ cardLength β x := hzh
    have hpi2 : ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ≤ 2 * cardLength β x := by
      linarith [hpi, hzR, hh1]
    have hpinn : (0 : ℝ) ≤ ((Nat.primesLE (ladderTop β γ x)).card : ℝ) := Nat.cast_nonneg _
    have hmnn : (0 : ℝ) ≤ mertensS (ladderTop β γ x) := mertensS_nonneg' _
    have hnum : (∑ n ∈ Finset.Icc 1 (budgetB β x),
          ‖omegaCoeff (primesRange (siftStart (γ * β) x) (ladderTop β γ x)) n‖ ^ 2)
        ≤ 8 * ((budgetB β x : ℕ) : ℝ) * mertensS (ladderTop β γ x)
          + 16 * cardLength β x + 64 * (cardLength β x) ^ 2
          + 2 * W ^ 2 * ((budgetB β x : ℕ) : ℝ) := by
      have hsq : ((Nat.primesLE (ladderTop β γ x)).card : ℝ) ^ 2
          ≤ 4 * (cardLength β x) ^ 2 := by nlinarith [hpi2, hpinn]
      linarith [hE, hpi2, hsq]
    rw [div_le_iff₀ hden]
    have hmaj0 : (0 : ℝ) ≤ 8 * (mertensS (ladderTop β γ x) / cardLength β x)
        + 16 * (1 / ((budgetB β x : ℕ) : ℝ))
        + 64 * (cardLength β x / ((budgetB β x : ℕ) : ℝ))
        + 2 * (1 / cardLength β x) := by positivity
    have hexp : (8 * (mertensS (ladderTop β γ x) / cardLength β x)
          + 16 * (1 / ((budgetB β x : ℕ) : ℝ))
          + 64 * (cardLength β x / ((budgetB β x : ℕ) : ℝ))
          + 2 * (1 / cardLength β x))
        * (((budgetB β x : ℕ) : ℝ) * cardLength β x * W ^ 2)
        = 8 * ((budgetB β x : ℕ) : ℝ) * mertensS (ladderTop β γ x) * W ^ 2
          + 16 * cardLength β x * W ^ 2 + 64 * (cardLength β x) ^ 2 * W ^ 2
          + 2 * W ^ 2 * ((budgetB β x : ℕ) : ℝ) := by
      field_simp
    rw [hexp]
    have hb1 : 8 * ((budgetB β x : ℕ) : ℝ) * mertensS (ladderTop β γ x)
        ≤ 8 * ((budgetB β x : ℕ) : ℝ) * mertensS (ladderTop β γ x) * W ^ 2 :=
      le_mul_of_one_le_right
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 8) hB0.le) hmnn) hW2
    have hb2 : 16 * cardLength β x ≤ 16 * cardLength β x * W ^ 2 :=
      le_mul_of_one_le_right (by linarith) hW2
    have hb3 : 64 * (cardLength β x) ^ 2 ≤ 64 * (cardLength β x) ^ 2 * W ^ 2 :=
      le_mul_of_one_le_right (by nlinarith [sq_nonneg (cardLength β x)]) hW2
    linarith [hnum, hb1, hb2, hb3]

end

end RHTower.Sieve
