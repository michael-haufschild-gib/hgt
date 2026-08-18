import GaloisForLFunctions.RHTower.Sieve.RhoLimit
import GaloisForLFunctions.RHTower.Sieve.NonSpectralBudget

/-!
# The elementary scale limits of the substitution

The window length is negligible against the outer scale, and the reciprocal step ratio is bounded by
the number of steps, so every quotient of the normalised budget reduces to `ρ·L → 0` and to
`h/B₀ → 0`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The window length is negligible against the fibre range. -/
theorem tendsto_cardLength_div_budgetB {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun x : ℝ => cardLength β x / ((budgetB β x : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun x : ℝ => cardLength β x / Real.sqrt x) atTop (𝓝 0) := by
    have hsq := tendsto_cardLength_sq_div_sqrt hβ0 hβ1
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      have := Real.sqrt_pos.2 hx
      have := cardLength_pos β x
      positivity
    · filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
        Filter.eventually_gt_atTop (0 : ℝ)] with x hh1 hx
      have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
      have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
      rw [div_le_div_iff₀ hsx hsx]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ cardLength β x)
        (by linarith : (0:ℝ) ≤ cardLength β x - 1)) hsx.le]
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have := cardLength_pos β x
    positivity
  · filter_upwards [(tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
      Filter.eventually_gt_atTop (0 : ℝ)] with x hh1 hx
    have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hB : Real.sqrt x ≤ ((budgetB β x : ℕ) : ℝ) := by
      rw [budgetB]
      have := Nat.lt_floor_add_one (Real.sqrt x + cardLength β x)
      linarith
    exact div_le_div_of_nonneg_left hh0.le hsx hB

/-- The reciprocal window length vanishes. -/
theorem tendsto_inv_cardLength {β : ℝ} (hβ0 : 0 < β) :
    Tendsto (fun x : ℝ => 1 / cardLength β x) atTop (𝓝 0) :=
  (tendsto_cardLength hβ0).const_div_atTop 1

/-- The reciprocal step ratio is bounded by twice the number of steps. -/
theorem eventually_inv_eta_le_steps {β γ : ℝ} (hβ0 : 0 < β) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hγβ : γ * β < 1) :
    ∀ᶠ x : ℝ in atTop,
      1 / ladderEta β γ x ≤ 2 * ((ladderSteps β γ x : ℕ) : ℝ) := by
  have hab : (0 : ℝ) < γ * β := mul_pos hγ0 hβ0
  have hzero := tendsto_ladderEta (β := β) (γ := γ) hβ0 hγβ
  have hpowA : Tendsto (fun x : ℝ => (Real.log x) ^ (γ * β)) atTop atTop :=
    (tendsto_rpow_atTop hab).comp Real.tendsto_log_atTop
  have hpowB : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ0).comp Real.tendsto_log_atTop
  have hpowD : Tendsto (fun x : ℝ => (Real.log x) ^ (β - γ * β)) atTop atTop :=
    (tendsto_rpow_atTop (by nlinarith)).comp Real.tendsto_log_atTop
  filter_upwards [Tendsto.eventually_le_const (by norm_num : (0:ℝ) < 1) hzero,
    Filter.eventually_gt_atTop (1 : ℝ), log_siftStart_le hab,
    hpowB.eventually_ge_atTop (4 : ℝ), hpowD.eventually_ge_atTop (2 * Real.log 2 + 4),
    hpowA.eventually_ge_atTop (Real.log 2 + 1)] with x hη1 hx1 hlogS hB4 hD2 hA1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < ladderEta β γ x := ladderEta_pos hx1
  have hQ0 : (0 : ℝ) < ((siftStart (γ * β) x : ℕ) : ℝ) := by
    have h1 : (1 : ℕ) ≤ siftStart (γ * β) x := by
      rw [siftStart]
      exact Nat.one_le_ceil_iff.2 (Real.exp_pos _)
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hsplit : (Real.log x) ^ β = (Real.log x) ^ (γ * β) * (Real.log x) ^ (β - γ * β) := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have hratio : (Real.log x) ^ β / 2
      ≤ Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ)) := by
    rw [Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0), log_cardLength]
    have hA0 : (0 : ℝ) < (Real.log x) ^ (γ * β) := Real.rpow_pos_of_pos hlogx _
    nlinarith [hlogS, hsplit, hD2, hA0, hA1,
      mul_nonneg hA0.le (by
        have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith : (0:ℝ) ≤ (Real.log x) ^ (β - γ * β) - 4)]
  have hlogr : Real.log (1 + ladderEta β γ x) ≤ ladderEta β γ x := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + ladderEta β γ x)
    linarith
  have hlogr0 : (0 : ℝ) < Real.log (1 + ladderEta β γ x) := Real.log_pos (by linarith)
  have hfl : Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
        / Real.log (1 + ladderEta β γ x) - 1
      ≤ ((ladderSteps β γ x : ℕ) : ℝ) := by
    rw [ladderSteps]
    have := Nat.lt_floor_add_one
      (Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
        / Real.log (1 + ladderEta β γ x))
    linarith
  have hdiv : (Real.log x) ^ β / (2 * ladderEta β γ x)
      ≤ Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ))
        / Real.log (1 + ladderEta β γ x) := by
    have hnum0 : (0 : ℝ) ≤ Real.log (cardLength β x / ((siftStart (γ * β) x : ℕ) : ℝ)) :=
      le_trans (by positivity) hratio
    refine (div_le_div₀ hnum0 hratio hlogr0 hlogr).trans' (le_of_eq ?_)
    field_simp
  have hkey : 1 / ladderEta β γ x + 2 ≤ (Real.log x) ^ β / ladderEta β γ x := by
    rw [div_add' _ _ _ (ne_of_gt hη), div_le_div_iff₀ hη hη]
    nlinarith [hB4, hη1, hη]
  have hchain : (Real.log x) ^ β / (2 * ladderEta β γ x) - 1
      ≤ ((ladderSteps β γ x : ℕ) : ℝ) := by linarith [hdiv, hfl]
  have hid : (Real.log x) ^ β / (2 * ladderEta β γ x)
      = (Real.log x) ^ β / ladderEta β γ x / 2 := by
    field_simp
  rw [hid] at hchain
  linarith [hchain, hkey]

end

end RHTower.Sieve
